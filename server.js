#!/usr/bin/env node
'use strict';

// FRAGMENT.IO GUEST MULTIPLAYER PATCH APPLIED

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const url = require('url');

const PORT = Number(process.env.PORT || 3000);
const ROOT = __dirname;
const WORLD_W = 9600, WORLD_H = 6400, HALF_W = WORLD_W / 2, HALF_H = WORLD_H / 2;
const MAX_SQUAD_PLAYERS = 6;
const MAX_FRAME_BYTES = 1024 * 1024;
const MAX_SOCKET_BACKLOG = 2 * 1024 * 1024;
const SUPPORTED_MODES = new Set(['normal','duo','squad','teams','br','bossrush']);
const DROPPABLE_PACKET_TYPES = new Set(['peer_state','bots_state','fragments_state','world_state','bosses_state']);
const rooms = new Map();
const clients = new Set();
const parties = new Map();
const matchQueues = new Map();
const userClients = new Map();
const reconnectReservations = new Map();
const pendingPartyInvites = new Map();
const playerReports = [];

const MODE_RULES = {
  normal:{capacity:15, partyMax:6, targetLow:8, targetMid:12, targetHigh:15, waitMs:8000, joinMid:true, spectate:true},
  duo:{capacity:12, partyMax:2, targetLow:8, targetMid:10, targetHigh:12, waitMs:9000, joinMid:true, spectate:true},
  squad:{capacity:6, partyMax:6, targetLow:18, targetMid:18, targetHigh:18, waitMs:9000, joinMid:true, spectate:true},
  teams:{capacity:20, partyMax:6, targetLow:12, targetMid:16, targetHigh:20, waitMs:10000, joinMid:true, spectate:true},
  br:{capacity:40, partyMax:4, targetLow:24, targetMid:32, targetHigh:40, waitMs:18000, joinMid:false, spectate:true},
  bossrush:{capacity:6, partyMax:6, targetLow:1, targetMid:3, targetHigh:6, waitMs:7000, joinMid:true, spectate:true},
  test:{capacity:1, partyMax:1, targetLow:1, targetMid:1, targetHigh:1, waitMs:0, joinMid:false, spectate:false}
};


function id(bytes = 8){ return crypto.randomBytes(bytes).toString('hex'); }
function cleanRoom(v){ return String(v || '').trim().toUpperCase().replace(/[^A-Z0-9-]/g, '').slice(0,18) || crypto.randomBytes(3).toString('hex').toUpperCase(); }
function safeName(v){ return String(v || 'Player').replace(/[<>]/g,'').slice(0,24) || 'Player'; }
function cleanMode(v){
  const mode = String(v || 'normal').toLowerCase();
  return SUPPORTED_MODES.has(mode) ? mode : 'normal';
}
function modeRules(mode){ return MODE_RULES[cleanMode(mode)] || MODE_RULES.normal; }
function roomCapacity(room){ return modeRules(room?.mode).capacity; }
function roomJoinWindowOpen(room){
  if(!room || !room.matchStarted) return false;
  const rules=modeRules(room.mode);
  if(!rules.joinMid || room.mode==='br' || room.mode==='test') return false;
  if(room.mode==='bossrush') return !!room.bossRushJoinOpen;
  return true;
}
function cleanUserId(v){ return String(v||'').trim().toLowerCase().replace(/[^a-f0-9-]/g,'').slice(0,36); }
function partyCode(){ return 'P-'+crypto.randomBytes(4).toString('hex').toUpperCase(); }
function matchCode(){ return 'M-'+crypto.randomBytes(5).toString('hex').toUpperCase(); }
function onlineClientForUser(userId){
  const set=userClients.get(String(userId||''));
  if(!set) return null;
  for(const client of set){ if(client.socket && !client.socket.destroyed) return client; }
  return null;
}
function allOnlineClientsForUser(userId){ return [...(userClients.get(String(userId||''))||[])].filter(c=>c.socket&&!c.socket.destroyed); }
function partyForClient(client){ return client?.partyId ? parties.get(client.partyId)||null : null; }
function privacyAllows(value, isFriend=true, isParty=false){
  const rule=String(value||'friends').toLowerCase();
  if(rule==='nobody') return false;
  if(rule==='party') return !!isParty;
  if(rule==='friends') return !!isFriend || !!isParty;
  return true;
}

function clamp(v, a, b){ return Math.max(a, Math.min(b, v)); }
function rand(a, b){ return a + Math.random() * (b - a); }
function irand(a, b){ return Math.floor(rand(a, b)); }
function dist(a, b){ return Math.hypot((a.x||0)-(b.x||0), (a.y||0)-(b.y||0)); }
function angleDiff(a, b){ return Math.atan2(Math.sin(a-b), Math.cos(a-b)); }
function finiteNumber(v, fallback=0, min=-Infinity, max=Infinity){
  const n = Number(v);
  return Number.isFinite(n) ? clamp(n, min, max) : fallback;
}
function safeToken(v, max=48){ return String(v || '').replace(/[^a-zA-Z0-9_:\-]/g,'').slice(0,max); }
function sameCombatTeam(a, b){ return !!a && !!b && a !== 'neutral' && b !== 'neutral' && a === b; }
function randomArenaPoint(minRadius=0, margin=360){
  for(let tries=0; tries<18; tries++){
    const p={x:rand(-HALF_W+margin, HALF_W-margin), y:rand(-HALF_H+margin, HALF_H-margin)};
    if(Math.hypot(p.x,p.y) >= minRadius) return p;
  }
  const ang=rand(0,Math.PI*2);
  const r=Math.max(minRadius, Math.min(HALF_W,HALF_H)-margin-80);
  return {x:Math.cos(ang)*r, y:Math.sin(ang)*r};
}
function teamForClient(room, client){
  if(['duo','squad','test'].includes(room.mode)) return 'blue';
  if(room.mode === 'teams'){
    if(client.matchTeam==='blue' || client.matchTeam==='red') return client.matchTeam;
    const list=[...room.clients];
    const blue=list.filter(c=>c!==client && c.serverTeam==='blue').length;
    const red=list.filter(c=>c!==client && c.serverTeam==='red').length;
    return blue<=red ? 'blue' : 'red';
  }
  return 'neutral';
}
function assignRoomTeams(room){
  for(const client of room.clients){
    client.serverTeam = teamForClient(room, client);
    if(client.snapshot) client.snapshot.team = client.serverTeam;
  }
}
function clientIsInvincible(client){
  if(!client || !client.snapshot || client.snapshot.dead) return true;
  return (client.spawnProtectedUntil||0) > Date.now() || finiteNumber(client.snapshot.spawnInvincible,0,0,20) > 0.03;
}
function sendDamageToClient(client, payload){
  if(!client || !client.inMatch || !client.snapshot || client.snapshot.dead || clientIsInvincible(client)) return false;
  return send(client, payload);
}
function sanitizeSnapshot(client, room, raw){
  raw = raw && typeof raw === 'object' ? raw : {};
  const previous = client.snapshot;
  const debugAuthorized=developerDebugSnapshotAuthorized(client);
  const playerMaxHpLimit=debugAuthorized?100000:1200;
  const maxHp = finiteNumber(raw.maxHp, finiteNumber(previous?.maxHp,100,1,playerMaxHpLimit), 1, playerMaxHpLimit);
  const dead = !!raw.dead;
  if((!previous && !dead) || (previous?.dead && !dead)){
    client.spawnProtectedUntil = Date.now() + 2600;
  }
  const snap = {...raw};
  snap.id = client.id;
  snap.userId = client.userId || "";
  snap.accountRole = publicAccountRole(client.accountRole);
  snap.entityId = safeToken(raw.entityId || '',64);
  snap.name = safeName(raw.name || client.name);
  snap.title = String(raw.title || '').replace(/[<>]/g,'').slice(0,40);
  snap.clan = String(raw.clan || '').replace(/[<>]/g,'').slice(0,20);
  snap.x = finiteNumber(raw.x, finiteNumber(previous?.x,0), -HALF_W, HALF_W);
  snap.y = finiteNumber(raw.y, finiteNumber(previous?.y,0), -HALF_H, HALF_H);
  snap.vx = finiteNumber(raw.vx,0,-80,80);
  snap.vy = finiteNumber(raw.vy,0,-80,80);
  snap.r = finiteNumber(raw.r,18,4,120);
  snap.angle = finiteNumber(raw.angle,0,-Math.PI*8,Math.PI*8);
  snap.maxHp = maxHp;
  snap.hp = finiteNumber(raw.hp,maxHp,0,maxHp);
  snap.level = Math.floor(finiteNumber(raw.level,1,1,999));
  snap.score = Math.floor(finiteNumber(raw.score,0,0,1e9));
  snap.frags = Math.floor(finiteNumber(raw.frags,0,0,1e6));
  snap.dead = dead;
  snap.team = client.serverTeam || teamForClient(room,client);
  const requestedArchetype=safeToken(raw.archetype || 'starter',48) || 'starter';
  const previousSafeArchetype=previous?.archetype&&previous.archetype!=='root_admin'
    ?safeToken(previous.archetype,48)
    :'starter';
  snap.archetype=(requestedArchetype==='root_admin'&&!debugAuthorized)
    ?previousSafeArchetype
    :requestedArchetype;
  snap.bodyColor = /^#[0-9a-fA-F]{3,8}$/.test(String(raw.bodyColor||'')) ? String(raw.bodyColor) : '#5d8cff';
  snap.skinKind = safeToken(raw.skinKind || 'circle',32) || 'circle';
  snap.spawnInvincible = finiteNumber(raw.spawnInvincible,0,0,20);
  snap.reflect = finiteNumber(raw.reflect,0,0,30);
  snap.bulletEater = finiteNumber(raw.bulletEater,0,0,30);
  snap.invisible = finiteNumber(raw.invisible,0,0,30);
  snap.abilities = Array.isArray(raw.abilities) ? raw.abilities.slice(0,5).map(v=>v==null?null:safeToken(v,48)) : [];
  snap.clones = Array.isArray(raw.clones) ? raw.clones.slice(0,3).map((clone,index)=>{
    clone = clone && typeof clone==='object' ? clone : {};
    const cloneMaxHp=finiteNumber(clone.maxHp,Math.max(1,maxHp*.55),1,debugAuthorized?100000:800);
    return {
      cloneId:safeToken(clone.cloneId||('clone_'+index),64)||('clone_'+index),
      name:safeName(clone.name||`${snap.name} Clone ${index+1}`),
      x:finiteNumber(clone.x,snap.x,-HALF_W,HALF_W),
      y:finiteNumber(clone.y,snap.y,-HALF_H,HALF_H),
      vx:finiteNumber(clone.vx,0,-80,80),
      vy:finiteNumber(clone.vy,0,-80,80),
      r:finiteNumber(clone.r,Math.max(10,snap.r*.82),4,90),
      angle:finiteNumber(clone.angle,snap.angle,-Math.PI*8,Math.PI*8),
      hp:finiteNumber(clone.hp,cloneMaxHp,0,cloneMaxHp),
      maxHp:cloneMaxHp,
      dead:!!clone.dead,
      archetype:(safeToken(clone.archetype||snap.archetype,48)==='root_admin'&&!debugAuthorized)
        ?'starter'
        :(safeToken(clone.archetype||snap.archetype,48)||snap.archetype),
      bodyColor:/^#[0-9a-fA-F]{3,8}$/.test(String(clone.bodyColor||''))?String(clone.bodyColor):'#66d98b',
      skinKind:safeToken(clone.skinKind||'circle',32)||'circle',
      invisible:finiteNumber(clone.invisible,0,0,30)
    };
  }) : [];
  return snap;
}

function makeRoom(code){
  return {
    code,
    clients:new Set(),
    spectators:new Set(),
    leaderId:null,
    mode:'normal',
    matchStarted:false,
    matchId:0,
    bots:[],
    fragments:[],
    bosses:[],
    world:{mode:null, timer:0, zones:[], nextAt:Date.now()+22000},
    terrainFeatures:[],
    hotZone:null,
    nextTerrainAt:Date.now()+9000,
    nextHotZoneAt:Date.now()+16000,
    lastTerrainSerial:0,
    lastBotBroadcast:0,
    lastShotSerial:0,
    lastFragmentSerial:0,
    lastFragmentBroadcast:0,
    lastBossSerial:0,
    lastBossBroadcast:0,
    lastWorldBroadcast:0,
    nextBossAt:Date.now()+32000,
    lastErrorAt:0,
    lastSquadLimitNotice:0,
    createdAt:Date.now(),
    startedAt:0,
    lastBackfillAt:0,
    emptySince:0,
    fillBots:true,
    completeRoster:true,
    matchmaking:false,
    bossRushJoinOpen:false,
    bossRushPhase:'closed'
  };
}
function getRoom(code){
  code = cleanRoom(code);
  if(!rooms.has(code)) rooms.set(code, makeRoom(code));
  return rooms.get(code);
}
function getClientById(room, clientId){
  for(const c of room.clients){ if(c.id === clientId) return c; }
  return null;
}
function chooseLeader(room){
  if(room.leaderId && getClientById(room, room.leaderId)) return;
  const first = room.clients.values().next().value;
  room.leaderId = first ? first.id : null;
}
function lobbyPayload(room){
  chooseLeader(room);
  assignRoomTeams(room);
  return {
    type:'lobby_state',
    room:room.code,
    leaderId:room.leaderId,
    mode:room.mode,
    matchStarted:room.matchStarted,
    players:[...room.clients].map(c=>({
      clientId:c.id,
      name:c.name,
      ready:!!c.ready,
      leader:c.id===room.leaderId,
      inMatch:!!c.inMatch,
      team:c.serverTeam||'neutral'
    }))
  };
}
function broadcastLobby(room){ broadcast(room.code, lobbyPayload(room)); }
function removeFromRoom(client,options={}){
  if(!client)return;
  const previousRoomCode=client.room;
  const party=partyForClient(client);
  let room=null,wasPlayer=false,wasSpectator=false;

  if(previousRoomCode){
    room=rooms.get(previousRoomCode);
    if(room){
      wasPlayer=room.clients.delete(client);
      wasSpectator=room.spectators?.delete(client)||false;
      if(wasPlayer){
        broadcast(room.code,{type:'peer_left',clientId:client.id,name:client.name},client);
      }
      chooseLeader(room);
      if(room.clients.size===0&&(!room.spectators||room.spectators.size===0)){
        if(room.matchStarted)room.emptySince=Date.now();
        else rooms.delete(previousRoomCode);
      }else if(wasPlayer){
        if(room.matchStarted&&room.mode!=='br')reconcileServerBots(room);
        broadcastLobby(room);
      }
    }
  }

  revokeDeveloperDebug(client,false);
  client.room=null;
  client.ready=false;
  client.inMatch=false;
  client.role='social';
  client.serverTeam='neutral';
  client.matchTeam=null;
  if(!options.keepSnapshot)client.snapshot=null;

  // Party membership is intentionally retained when leaving a match.
  if(party){
    party.queued=false;
    party.queueId=null;
    if(party.ready.has(client.userId)&&client.userId!==party.leaderId){
      party.ready.set(client.userId,false);
    }
    broadcastParty(party);
  }

  if(wasPlayer||wasSpectator||previousRoomCode){
    broadcastPresenceForUser(client.userId);
  }
}
function send(client, obj){
  if(!client || !client.socket || client.socket.destroyed || !client.socket.writable) return false;
  try{
    if(client.socket.writableLength > MAX_SOCKET_BACKLOG && DROPPABLE_PACKET_TYPES.has(obj?.type)) return false;
    const data = Buffer.from(JSON.stringify(obj));
    if(data.length > MAX_FRAME_BYTES) return false;
    let header;
    if(data.length < 126){
      header = Buffer.from([0x81, data.length]);
    }else if(data.length < 65536){
      header = Buffer.alloc(4);
      header[0] = 0x81; header[1] = 126; header.writeUInt16BE(data.length, 2);
    }else{
      header = Buffer.alloc(10);
      header[0] = 0x81; header[1] = 127; header.writeBigUInt64BE(BigInt(data.length), 2);
    }
    client.socket.write(Buffer.concat([header, data]));
    return true;
  }catch(e){
    return false;
  }
}
function broadcast(roomCode, obj, except=null){
  const room = rooms.get(roomCode);
  if(!room) return;
  for(const client of room.clients){ if(client !== except) send(client, obj); }
  for(const client of (room.spectators||[])){ if(client !== except) send(client, obj); }
}
function peersFor(client){
  const room = rooms.get(client.room);
  if(!room) return [];
  const peers = [];
  for(const peer of room.clients){
    if(peer !== client && peer.snapshot) peers.push({clientId:peer.id, name:peer.name, snapshot:peer.snapshot});
  }
  return peers;
}

const botNames = ['Echo','Mira','Waltz','Kite','Phantom','Ivy','Rook','Bolt','June','Quartz','HomingBug','Needle','Comet','Vector','Orbit','FlareFox','Drift','Cannon','Sable','Nova','Atlas','Vega','Pixel','Frost','Rift','Juno','Nyx','Astra','Mako','Rune','Vale','Onyx','Luma','Cinder','Glitch','Delta','Zero','Solar','Iris','Vortex','Prism','Flux','Ash','Cobalt','Ember','Halo','Zenith','Crow','Pico','Blade'];
const archetypes = ['starter','swordsman','ronin','azure','solar_lance','hakka','deadeye','hydra','world_eater','black_star','bloodlord','bullet_storm','machine','minigunner','sniper','rocketeer','gravity_mage','stormcaller'];
const BR_SERVER_BOT_PATHS=[
  ['starter','swordsman','samurai','ronin'],
  ['starter','kindler','hellflame','azure'],
  ['starter','sniper','marksman','deadeye'],
  ['starter','machine','minigunner','bullet_storm'],
  ['starter','cloner','doppelgaenger','hakka'],
  ['starter','gravity_mage','singularity','black_star'],
  ['starter','rocketeer','destroyer','warhead'],
  ['starter','spark','stormcaller','thunder_god']
];
const colors = ['#ff775d','#6a7cf7','#53b07b','#ffcf58','#76d7ff','#cb80ff','#d84a4a','#9aa9b8'];
function targetPopulationForMode(mode,humanCount){
  mode=cleanMode(mode);
  if(mode==='bossrush') return humanCount;
  if(mode==='squad') return 18;
  return modeRules(mode).capacity;
}
function botCountForMode(mode,humanCount=1,fillBots=true){
  if(mode==='bossrush') return 0;
  return Math.max(0,targetPopulationForMode(mode,humanCount)-humanCount);
}
function teamForBot(room,i,count){
  const mode=room?.mode||'normal';
  if(mode==='teams'){
    const perTeam=Math.floor(modeRules('teams').capacity/2);
    const blueHumans=[...room.clients].filter(client=>(client.serverTeam||client.matchTeam)==='blue').length;
    const redHumans=[...room.clients].filter(client=>(client.serverTeam||client.matchTeam)==='red').length;
    const blueNeed=Math.max(0,perTeam-blueHumans);
    return i<blueNeed?'blue':'red';
  }
  if(mode==='squad'){
    const alliedNeed=room.completeRoster!==false
      ?Math.max(0,6-room.clients.size)
      :0;
    return i<alliedNeed?'blue':'red';
  }
  if(mode==='duo') return 'red';
  return 'neutral';
}
function createServerBot(room,i,count){
  const team = teamForBot(room, i, count);
  const passive = false;
  const namePrefix = room.mode === 'br' ? 'BR ' : room.mode === 'teams' ? (team === 'blue' ? 'Blue ' : 'Red ') : room.mode === 'squad' ? (team==='blue'?'Squad ':'Enemy ') : '';
  const point = room.mode === 'test'
    ? {x:((i % 4) - 1.5) * 260, y:(Math.floor(i / 4) - 1) * 230}
    : randomArenaPoint(720,360);
  const roam = randomArenaPoint(620,260);
  return {
    id:'bot_' + id(5),
    name: passive ? `Dummy ${String(i+1).padStart(2,'0')}` : `${namePrefix}${botNames[i % botNames.length]}-${String(i+1).padStart(2,'0')}`,
    x:point.x, y:point.y,
    vx:0, vy:0, r:18, angle:rand(0, Math.PI*2),
    hp: passive ? 280 : 115, maxHp: passive ? 280 : 115,
    score:0, frags:0, level:1,
    team, ally:team === 'blue', passive,
    archetype: room.mode==='br'?'starter':archetypes[i % archetypes.length],
    brPathIndex:i%BR_SERVER_BOT_PATHS.length, brEvolutionStage:0,
    bodyColor: passive ? '#7fd8ff' : colors[i % colors.length],
    fireCd:room.mode==='br'?rand(3.0,4.2):rand(1.3,2.1), think:0, strafe:Math.random()<0.5 ? -1 : 1,
    aimError:rand(-0.10,0.10), dodge:rand(.75,1.25), confidence:room.mode==='br'?rand(.52,.88):rand(.75,1.22),
    meleeCd:rand(.9,1.5), lastTargetId:null, targetLockUntil:0,
    personality:['duelist','hunter','scavenger','coward','roamer'][i%5],
    roamX:roam.x, roamY:roam.y,
    spawnGraceUntil:room.mode==='br'?Date.now()+32000:Date.now()+rand(1700,2600),
    dead:false, respawnAt:0, lastHitBy:null
  };
}
function spawnServerBots(room){
  room.bots = [];
  if(room.mode==='bossrush') return;
  const count = botCountForMode(room.mode,room.clients.size,room.fillBots!==false);
  for(let i=0;i<count;i++) room.bots.push(createServerBot(room,i,count));
}
function reconcileServerBots(room){
  if(!room || !room.matchStarted || room.mode==='br') return;
  if(room.mode==='bossrush'){
    room.bots=[];
    broadcast(room.code,{type:'bots_state',mode:room.mode,bots:[],immediate:true});
    return;
  }
  const desired=botCountForMode(room.mode,room.clients.size,room.fillBots!==false);
  while(room.bots.length>desired){
    const deadIndex=room.bots.findIndex(b=>b.dead);
    room.bots.splice(deadIndex>=0?deadIndex:room.bots.length-1,1);
  }
  while(room.bots.length<desired){
    room.bots.push(createServerBot(room,room.bots.length,desired));
  }
  broadcast(room.code,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot),immediate:true});
}

function publicPlayerCard(client){
  const profile=client?.profile||{},progress=client?.progress||{},stats=progress.stats||{};
  return {userId:client?.userId||'',username:profile.username||client?.name||'Player',title:profile.equipped_title||'',banner:profile.profile_banner||'default',icon:profile.profile_icon||'core:circle',level:Number(progress.account_level)||1,achievementPoints:Number(progress.achievement_points)||0,favoriteEvolution:String(stats.favorite_evolution||''),showcasedAchievement:(profile.featured_achievements||progress.showcased_achievements||[])[0]||'',accountRole:publicAccountRole(client?.accountRole)};
}
function roomPlayerCards(room){return [...room.clients].filter(c=>c.authenticated&&c.userId).map(publicPlayerCard);}

function startMatch(room){
  room.matchStarted = true;
  room.matchId++;
  assignRoomTeams(room);
  const now=Date.now();
  room.startedAt=now;
  room.brCombatStartsAt=room.mode==='br'?now+30000:now;
  room.lastBackfillAt=now;
  room.bossRushJoinOpen=room.mode==='bossrush';
  room.bossRushPhase=room.mode==='bossrush'?'preparation':'closed';
  for(const c of room.clients){
    c.inMatch = true;
    c.spawnProtectedUntil = now + 2600;
    if(c.snapshot) c.snapshot.team = c.serverTeam;
  }
  spawnServerBots(room);
  initSharedWorld(room);
  const botsState = {type:'bots_state', mode:room.mode, bots:room.bots.map(botSnapshot), immediate:true};
  broadcast(room.code, {type:'match_start', mode:room.mode, matchId:room.matchId, startedAt:now, playerCards:roomPlayerCards(room)});
  broadcast(room.code, botsState);
  broadcastSharedState(room, true);
  broadcastLobby(room);
}
function maybeStartMatch(room){
  if(room.matchStarted) return;
  if(room.clients.size < 2) return;
  if(room.mode === 'squad' && room.clients.size > MAX_SQUAD_PLAYERS){
    const now=Date.now();
    if(now-(room.lastSquadLimitNotice||0)>1800){
      room.lastSquadLimitNotice=now;
      broadcast(room.code,{type:'chat',name:'SERVER',msg:`Squad mode supports up to ${MAX_SQUAD_PLAYERS} players. Remove extra players before readying.`});
    }
    for(const c of room.clients) c.ready=false;
    broadcastLobby(room);
    return;
  }
  for(const c of room.clients){ if(!c.ready) return; }
  startMatch(room);
}
function botSnapshot(bot){
  return {
    id:bot.id,
    name:bot.name,
    x:Math.round(bot.x*10)/10, y:Math.round(bot.y*10)/10,
    vx:Math.round(bot.vx*100)/100, vy:Math.round(bot.vy*100)/100,
    r:bot.r, angle:bot.angle,
    hp:Math.max(0, Math.round(bot.hp*10)/10), maxHp:bot.maxHp,
    dead:!!bot.dead, score:Math.floor(bot.score||0), frags:bot.frags||0, level:bot.level||1,
    team:bot.team, ally:!!bot.ally, archetype:bot.archetype, bodyColor:bot.bodyColor,
    passive:!!bot.passive
  };
}
function livePlayerSnapshots(room){
  return [...room.clients]
    .filter(c=>c.snapshot && !c.snapshot.dead && c.inMatch)
    .map(c=>({client:c, ...c.snapshot}));
}
function botCanTarget(bot,target){
  if(!target||target.dead)return false;
  if(sameCombatTeam(bot.team,target.team))return false;
  if(target.kind==='player'){
    if(clientIsInvincible(target.client))return false;
    if(finiteNumber(target.invisible,target.client?.snapshot?.invisible||0,0,30)>0.03)return false;
  }
  if(target.kind==='clone'){
    if(!target.client?.inMatch||target.client?.snapshot?.dead)return false;
    if(finiteNumber(target.invisible,0,0,30)>0.03)return false;
  }
  return true;
}
function nearestTargetForBot(room,bot){
  const now=Date.now();
  const candidates=[];

  for(const snap of livePlayerSnapshots(room)){
    const team=snap.client.serverTeam||snap.team||'neutral';
    candidates.push({
      kind:'player',
      id:snap.client.id,
      key:'player:'+snap.client.id,
      name:snap.name||snap.client.name,
      client:snap.client,
      x:snap.x||0,y:snap.y||0,vx:snap.vx||0,vy:snap.vy||0,
      hp:snap.hp||1,maxHp:snap.maxHp||1,
      team,
      dead:!!snap.dead,
      invisible:finiteNumber(snap.invisible,0,0,30),
      human:true
    });

    for(const clone of (snap.clones||[])){
      if(!clone||clone.dead)continue;
      candidates.push({
        kind:'clone',
        id:snap.client.id+':'+clone.cloneId,
        key:'clone:'+snap.client.id+':'+clone.cloneId,
        name:clone.name||((snap.name||snap.client.name)+' Clone'),
        client:snap.client,
        cloneId:clone.cloneId,
        x:clone.x||snap.x||0,
        y:clone.y||snap.y||0,
        vx:clone.vx||0,
        vy:clone.vy||0,
        hp:clone.hp||1,
        maxHp:clone.maxHp||1,
        team,
        dead:!!clone.dead,
        invisible:finiteNumber(clone.invisible,0,0,30),
        human:false
      });
    }
  }

  for(const other of room.bots){
    if(other===bot||other.dead)continue;
    candidates.push({
      kind:'bot',
      id:other.id,
      key:'bot:'+other.id,
      name:other.name,
      bot:other,
      x:other.x,y:other.y,vx:other.vx||0,vy:other.vy||0,
      hp:other.hp,maxHp:other.maxHp,
      team:other.team||'neutral',
      dead:!!other.dead,
      human:false
    });
  }

  const locked=candidates.find(target=>target.key===bot.lastTargetId);
  if(locked&&bot.targetLockUntil>now&&botCanTarget(bot,locked)){
    const distance=dist(bot,locked);
    if(distance<1250)return{snap:locked,d:distance};
  }

  let best=null,bestScore=-Infinity;
  for(const target of candidates){
    if(!botCanTarget(bot,target))continue;
    const distance=dist(bot,target);
    if(distance>1220)continue;
    const hpRatio=clamp((target.hp||1)/Math.max(1,target.maxHp||1),0,1);
    let assigned=0;
    for(const other of room.bots){
      if(other!==bot&&!other.dead&&other.lastTargetId===target.key)assigned++;
    }
    let score=-distance*.43+(1-hpRatio)*165-assigned*62;
    if(target.kind==='bot')score+=46;
    else if(target.kind==='clone')score+=31;
    else score+=8;
    if(bot.lastHitBy===target.id)score+=240;
    if(distance<300)score+=74;
    if(bot.personality==='hunter')score+=(1-hpRatio)*90;
    if(bot.personality==='scavenger'&&hpRatio>.62)score-=85;
    if(bot.personality==='coward'&&distance<260&&target.hp>bot.hp)score-=150;
    if(score>bestScore){bestScore=score;best=target;}
  }

  if(!best)return null;
  bot.lastTargetId=best.key;
  bot.targetLockUntil=now+rand(850,1750);
  return{snap:best,d:dist(bot,best)};
}
function killServerBot(room, bot, source){
  if(!bot || bot.dead) return;
  bot.dead=true;
  bot.hp=0;
  bot.respawnAt=Date.now()+(room.mode==='br'?999999999:3200);
  bot.lastTargetId=null;

  const dropCount=room.mode==='br'?8:11;
  spawnDeathFragmentBurst(room,bot.x,bot.y,dropCount,'bot_death',.26);

  if(source?.kind==='player' && source.client){
    send(source.client,{type:'bot_award',botId:bot.id,botName:bot.name,xp:40,score:250});
  }else if(source?.kind==='bot' && source.bot){
    source.bot.score=(source.bot.score||0)+260;source.bot.frags=(source.bot.frags||0)+2;source.bot.level=1+Math.floor(source.bot.score/700);
  }
  broadcast(room.code,{
    type:'bot_killed',
    botId:bot.id,
    botName:bot.name,
    killerId:source?.id||'',
    killerName:source?.name||'Environment'
  });
}
function damageServerBot(room, bot, amount, source){
  if(!bot || bot.dead) return false;
  const dmg=clamp(finiteNumber(amount,0),0,500);
  if(dmg<=0) return false;
  bot.hp-=dmg;
  bot.lastHitBy=source?.id||null;
  if(bot.hp<=0) killServerBot(room,bot,source);
  return true;
}
function deliverBotDamage(room,attacker,target,amount,cause){
  if(!target||!botCanTarget(attacker,target))return false;
  amount=clamp(finiteNumber(amount,0)*1.18,0,500);
  attacker.score=(attacker.score||0)+Math.max(1,Math.round(amount*6));
  attacker.frags=(attacker.frags||0)+(Math.random()<.08?1:0);
  attacker.level=1+Math.floor((attacker.score||0)/700);

  if(target.kind==='player'){
    return sendDamageToClient(target.client,{
      type:'bot_hit',
      botId:attacker.id,
      botName:attacker.name,
      amount,
      cause
    });
  }

  if(target.kind==='clone'){
    return send(target.client,{
      type:'bot_hit',
      botId:attacker.id,
      botName:attacker.name,
      cloneId:target.cloneId,
      amount,
      cause
    });
  }

  if(target.kind==='bot'){
    return damageServerBot(room,target.bot,amount,{
      kind:'bot',
      id:attacker.id,
      name:attacker.name,
      bot:attacker
    });
  }

  return false;
}

function broadcastBotProjectile(room, bot, angle, options){
  broadcast(room.code,{
    type:'bot_projectile',
    botId:bot.id,
    bot:botSnapshot(bot),
    angle,
    options:{...options,visualOnly:true,networkReplay:true},
    serial:++room.lastShotSerial
  });
}
function broadcastBotAction(room, bot, action, data={}){
  broadcast(room.code,{
    type:'bot_action',
    botId:bot.id,
    bot:botSnapshot(bot),
    action,
    angle:finiteNumber(data.angle,bot.angle,-Math.PI*8,Math.PI*8),
    range:finiteNumber(data.range,120,0,1800),
    width:finiteNumber(data.width,20,0,180),
    color:String(data.color||bot.bodyColor||'#ffffff').slice(0,24),
    duration:finiteNumber(data.duration,.22,.03,4),
    label:String(data.label||'').slice(0,30)
  });
}
function botProjectileHitChance(bot,target,shotAngle,base=.28){
  const trueAngle=Math.atan2(target.y-bot.y,target.x-bot.x);
  const error=Math.abs(angleDiff(shotAngle,trueAngle));
  const d=dist(bot,target);
  const distanceBonus=clamp(1-d/940,.04,.58);
  return {
    error,
    chance:clamp(base+distanceBonus*.42-error*.92,.05,.72)*clamp(bot.confidence||.85,.55,1)
  };
}
function tryBotProjectileDamage(room,bot,target,shotAngle,damage,baseAccuracy,cause='projectile'){
  const roll=botProjectileHitChance(bot,target,shotAngle,baseAccuracy);
  if(roll.error<.36 && Math.random()<roll.chance){
    deliverBotDamage(room,bot,target,damage,cause);
    return true;
  }
  return false;
}
function performServerBotClassAttack(room,bot,target,angle,distance){
  const a=bot.archetype||'starter';
  const col=bot.bodyColor||'#ff775d';
  const shoot=(ang,opt,accuracy=.28,cause='projectile')=>{
    broadcastBotProjectile(room,bot,ang,opt);
    return tryBotProjectileDamage(room,bot,target,ang,opt.dmg||5,accuracy,cause);
  };

  if(['swordsman','samurai','ronin','bloodlord'].includes(a)){
    const range=a==='ronin'?150:a==='bloodlord'?138:126;
    const dmg=a==='ronin'?8.2:a==='bloodlord'?7.1:6.4;
    broadcastBotAction(room,bot,'slice',{angle,range,color:a==='bloodlord'?'#d84a4a':'#e9f5ff',label:a==='ronin'?'RONIN SLASH':a==='bloodlord'?'BLOOD CUT':'SWORD CUT'});
    if(distance<range+18){
      const hit=deliverBotDamage(room,bot,target,dmg,'class_melee');
      if(hit && a==='bloodlord') bot.hp=Math.min(bot.maxHp,bot.hp+dmg*.32);
    }
    return rand(.88,1.24);
  }

  if(a==='world_eater'){
    broadcastBotAction(room,bot,'aura',{range:185,color:'#8f6cff',duration:.4,label:'DEVOUR'});
    if(distance<190) deliverBotDamage(room,bot,target,6.4,'devour_aura');
    return rand(1.0,1.35);
  }

  if(a==='solar_lance'){
    broadcastBotAction(room,bot,'beam',{angle,range:820,width:34,color:'#fff06a',duration:.38,label:'SOLAR LANCE'});
    const roll=botProjectileHitChance(bot,target,angle,.42);
    if(distance<820 && roll.error<.085 && Math.random()<Math.min(.78,roll.chance+.16)){
      deliverBotDamage(room,bot,target,10.2,'solar_lance');
    }
    return rand(1.35,1.75);
  }

  if(a==='azure'){
    shoot(angle,{
      kind:'fireball',speed:6.4,life:86,dmg:6.1,color:'#45d8ff',size:8,
      aoeRadius:72,burnDuration:1.1,burnDmg:1.2,burnColor:'#45d8ff',azure:true,
      noPool:true,proxRadius:52
    },.27,'azure_fire');
    return rand(.88,1.15);
  }

  if(a==='hakka'){
    shoot(angle,{kind:'hive',speed:8.2,life:98,dmg:5.2,color:'#66d98b',size:5,homing:true,split:true,splitAt:40},.31,'hakka_round');
    broadcastBotProjectile(room,bot,angle+.15,{kind:'basic',speed:7.8,life:78,dmg:2.8,color:'#a6ffb9',size:3});
    broadcastBotProjectile(room,bot,angle-.15,{kind:'basic',speed:7.8,life:78,dmg:2.8,color:'#a6ffb9',size:3});
    return rand(.82,1.08);
  }

  if(a==='deadeye' || a==='sniper'){
    const crit=a==='deadeye' && Math.random()<.26;
    shoot(angle+rand(-.035,.035),{
      kind:'basic',speed:11.2,life:155,dmg:crit?11.5:8.6,color:crit?'#ffcf58':'#15191f',size:crit?6:4,crit
    },.42,'precision_round');
    return rand(1.18,1.62);
  }

  if(a==='hydra'){
    const spread=[-.24,-.12,0,.12,.24];
    for(const offset of spread){
      broadcastBotProjectile(room,bot,angle+offset,{kind:'basic',speed:7.6,life:84,dmg:2.5,color:'#263547',size:4});
    }
    tryBotProjectileDamage(room,bot,target,angle,6.8,.25,'hydra_volley');
    return rand(1.02,1.34);
  }

  if(a==='rocketeer'){
    shoot(angle,{
      kind:'rocket',speed:5.4,life:165,dmg:8.4,color:'#ff775d',size:9,guided:true,homing:true,explode:true,explodeRadius:82
    },.29,'rocket');
    return rand(1.2,1.58);
  }

  if(a==='black_star' || a==='gravity_mage'){
    shoot(angle,{
      kind:'gravity',speed:6.6,life:135,dmg:a==='black_star'?8.4:6.7,color:a==='black_star'?'#17131f':'#9d80ff',
      size:a==='black_star'?10:7,homing:true,gravityPower:a==='black_star'?18:12,gravityRadius:a==='black_star'?155:110,
      createWell:false,blackStar:a==='black_star'
    },.31,'gravity_orb');
    return rand(1.12,1.48);
  }

  if(a==='stormcaller'){
    broadcastBotAction(room,bot,'lightning',{angle,range:250,color:'#8ae4ff',duration:.28,label:'CHAIN LIGHTNING'});
    shoot(angle,{
      kind:'basic',speed:10.1,life:90,dmg:6.8,color:'#8ae4ff',size:6,jumps:2,chainRange:190,staticStacks:1
    },.34,'lightning');
    return rand(.98,1.28);
  }

  if(['bullet_storm','machine','minigunner'].includes(a)){
    const storm=a==='bullet_storm';
    shoot(angle+rand(storm?-.12:-.07,storm?.12:.07),{
      kind:'basic',speed:8.6,life:72,dmg:storm?3.8:4.4,color:'#262d37',size:4
    },storm?.18:.23,'automatic_fire');
    if(storm && Math.random()<.34){
      broadcastBotProjectile(room,bot,angle+rand(-.18,.18),{kind:'basic',speed:8.3,life:68,dmg:2.4,color:'#596574',size:3});
    }
    return storm?rand(.32,.48):rand(.48,.68);
  }

  shoot(angle+rand(-.09,.09),{kind:'basic',speed:7.7,life:94,dmg:5.4,color:col,size:5},.27,'basic');
  return rand(.78,1.08);
}

function updateServerBots(room, dt){
  if(!room.matchStarted || !room.bots.length) return;
  const now=Date.now();
  const step=dt/16.6;

  for(const bot of room.bots){
    if(!Number.isFinite(bot.x)||!Number.isFinite(bot.y)||!Number.isFinite(bot.vx)||!Number.isFinite(bot.vy)){
      const p=randomArenaPoint(900,420);
      bot.x=p.x; bot.y=p.y; bot.vx=0; bot.vy=0;
    }

    if(bot.dead){
      if(room.mode!=='br' && now>=bot.respawnAt){
        const occupied=room.bots.filter(o=>o!==bot&&!o.dead);
        let p=randomArenaPoint(900,420);
        for(let tries=0;tries<50;tries++){
          const candidate=randomArenaPoint(900,420);
          if(occupied.every(o=>dist(o,candidate)>520)){ p=candidate; break; }
        }
        const roam=randomArenaPoint(900,420);
        bot.dead=false; bot.hp=bot.maxHp; bot.x=p.x; bot.y=p.y;
        bot.vx=0; bot.vy=0; bot.fireCd=rand(2.2,3.3); bot.meleeCd=rand(1.4,2.2);
        bot.lastHitBy=null; bot.lastTargetId=null; bot.targetLockUntil=0;
        bot.roamX=roam.x; bot.roamY=roam.y; bot.spawnGraceUntil=now+rand(2700,3700);
      }
      continue;
    }

    if(bot.passive){
      bot.vx*=.88; bot.vy*=.88; bot.angle+=dt*.00055;
      continue;
    }

    bot.think-=dt/1000;
    if(bot.think<=0){
      bot.think=rand(.35,.8);
      if(Math.random()<.28) bot.strafe*=-1;
      if(Math.random()<.20){
        const roam=randomArenaPoint(900,420);
        bot.roamX=roam.x; bot.roamY=roam.y;
      }
    }

    const target=nearestTargetForBot(room,bot);
    let mx=0,my=0;

    if(target){
      const t=target.snap;
      const predictedX=t.x+(t.vx||0)*5;
      const predictedY=t.y+(t.vy||0)*5;
      const ang=Math.atan2(predictedY-bot.y,predictedX-bot.x);
      bot.angle=ang;
      const tx=Math.cos(ang),ty=Math.sin(ang);
      const sx=-ty*bot.strafe,sy=tx*bot.strafe;
      const desired=bot.desiredRange||300;
      const low=bot.hp<bot.maxHp*.28;

      if(low && target.d<450){
        mx-=tx*1.05; my-=ty*1.05; mx+=sx*.35; my+=sy*.35;
      }else if(target.d>desired+95){
        mx+=tx*.88; my+=ty*.88; mx+=sx*.14; my+=sy*.14;
      }else if(target.d<desired-75){
        mx-=tx*.78; my-=ty*.78; mx+=sx*.30; my+=sy*.30;
      }else{
        mx+=sx*.62; my+=sy*.62;
      }

      bot.fireCd=Math.max(0,bot.fireCd-dt/1000);
      bot.meleeCd=Math.max(0,bot.meleeCd-dt/1000);

      if(now>=bot.spawnGraceUntil){
        const melee=['ronin','swordsman','world_eater','bloodlord'].includes(bot.archetype);
        if(melee && target.d<105 && bot.meleeCd<=0){
          bot.meleeCd=rand(.9,1.35);
          deliverBotDamage(room,bot,t,bot.archetype==='ronin'?7.5:6,'melee');
        }

        if(bot.fireCd<=0 && target.d<860){
          bot.fireCd=performServerBotClassAttack(room,bot,t,ang,target.d);
        }
      }
    }else{
      const dx=bot.roamX-bot.x,dy=bot.roamY-bot.y,L=Math.hypot(dx,dy)||1;
      if(L<120){
        const roam=randomArenaPoint(900,420);
        bot.roamX=roam.x; bot.roamY=roam.y;
      }
      mx+=dx/L*.58; my+=dy/L*.58; bot.angle=Math.atan2(dy,dx);
    }

    // Strong physical separation. This is computed once on the authoritative
    // server, so every player sees the same non-stacked bot positions.
    let closeCount=0;
    for(const other of room.bots){
      if(other===bot||other.dead) continue;
      const dx=bot.x-other.x,dy=bot.y-other.y,d=Math.hypot(dx,dy);
      if(d>0&&d<260){
        const force=Math.pow((260-d)/260,.62);
        mx+=(dx/d)*force*2.7;
        my+=(dy/d)*force*2.7;
        closeCount++;
      }
    }

    // Do not let the entire roster idle in the middle.
    const centerD=Math.hypot(bot.x,bot.y);
    if(centerD<720 && closeCount>=2){
      mx+=(bot.x/(centerD||1))*.75;
      my+=(bot.y/(centerD||1))*.75;
    }

    if(bot.x<-HALF_W+300) mx+=1;
    if(bot.x> HALF_W-300) mx-=1;
    if(bot.y<-HALF_H+300) my+=1;
    if(bot.y> HALF_H-300) my-=1;

    const mag=Math.hypot(mx,my)||1;
    const speed=['ronin','swordsman'].includes(bot.archetype)?3.45:2.85;
    bot.vx=bot.vx*.82+(mx/mag)*speed*.18;
    bot.vy=bot.vy*.82+(my/mag)*speed*.18;
    bot.x=clamp(bot.x+bot.vx*step,-HALF_W+30,HALF_W-30);
    bot.y=clamp(bot.y+bot.vy*step,-HALF_H+30,HALF_H-30);
  }

  // 8 Hz snapshots are smooth enough with interpolation and much cheaper than 10 Hz.
  if(now-room.lastBotBroadcast>125){
    room.lastBotBroadcast=now;
    broadcast(room.code,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)});
  }
}

function terrainSnapshot(f){
  return {id:f.id, type:f.type, x:Math.round(f.x*10)/10, y:Math.round(f.y*10)/10, life:Math.max(0,Math.round((f.life||0)*1000)), spawn:Math.max(0,Math.round((f.spawn||0)*1000)), r:Math.round(f.r||100), angle:f.angle||0};
}
function setSharedHotZone(room){
  const b = sharedBiomes[irand(0, sharedBiomes.length)];
  room.hotZone = {biome:b, timer:75, pulse:0, id:'hot_'+id(4)};
  room.nextHotZoneAt = Date.now() + rand(85000,110000);
  broadcast(room.code, {type:'hotzone_event', action:'set', hotZone:hotZoneSnapshot(room.hotZone)});
}
function hotZoneSnapshot(h){
  if(!h) return null;
  return {id:h.id, biome:h.biome, timer:Math.max(0, Math.round((h.timer||0)*1000)), pulse:h.pulse||0};
}
function updateSharedMapSystems(room, dt){
  if(!room.matchStarted || room.mode === 'bossrush') return;
  const now=Date.now();
  if(!room.hotZone && now > (room.nextHotZoneAt||0) && !['test','br'].includes(room.mode)) setSharedHotZone(room);
  if(room.hotZone){
    room.hotZone.timer = Math.max(0, room.hotZone.timer - dt/1000);
    room.hotZone.pulse = (room.hotZone.pulse||0) + dt/1000;
    if(room.hotZone.timer<=0){ room.hotZone=null; room.nextHotZoneAt=now+rand(85000,112000); broadcast(room.code, {type:'hotzone_event', action:'clear'}); }
    else if(Math.random()<0.035){
      const b=room.hotZone.biome;
      spawnSharedFragment(room, Math.random()<0.78?'xp':Math.random()<0.65?'natural':'ability', b.x+rand(60,b.w-60), b.y+rand(60,b.h-60));
    }
  }
  if(now > (room.nextTerrainAt||0) && !['test','br'].includes(room.mode)){
    room.nextTerrainAt = now + rand(9000,13500);
    if(Math.random()<.78) spawnSharedTerrainFeature(room);
  }
  for(let i=room.terrainFeatures.length-1;i>=0;i--){
    const f=room.terrainFeatures[i];
    f.life -= dt/1000;
    f.spawn = Math.max(0, (f.spawn||0)-dt/1000);
    if(f.life<=0) room.terrainFeatures.splice(i,1);
  }
}

// -----------------------------
// Shared online map state
// -----------------------------
const abilityIds = ['dash','blink','fireball','gravity_aura','lightning','poison_dart','regeneration','bullet_spam','freeze_ray','gravity_bullet','magnet','knockback','precision_strike','flare','ricochet_dart','reflect_shield','fragment_mine','judgement_laser','bullet_eater','fragment_storm','loot_radar','wall_drop'];
const coreIds = ['mirror','void','titan','glass','gravity','blood','frost','memory','ember','swift','reach','echo'];
const worldDefs = [
  {key:'frozen', name:'Frozen World', color:'#6ca7d8', desc:'Ice fields form around the map and heavily slow anyone inside.'},
  {key:'overgrowth', name:'Overgrowth', color:'#4d9460', desc:'Vine gardens slow movement but grow natural fragments.'},
  {key:'corruption', name:'Corruption Bloom', color:'#70429c', desc:'Void blooms drain health but can crystallize into rare fragments.'},
  {key:'golden', name:'Golden Rain', color:'#d6a84a', desc:'Golden showers create safe loot zones and bonus fragments.'}
];
const bossDefs = [
  {id:'elevator_authority', name:'The Elevator Authority', color:'#ffcf58', skin:'elevatorpanel', archetype:'spark', hp:1320, r:48, speed:0.96, desc:'Floor 7 administrative boss.'},
  {id:'telomere_warden', name:'Telomere Warden', color:'#75ffb2', skin:'forbiddentelomere', archetype:'gravity_mage', hp:1280, r:46, speed:1.08, desc:'Immortal biotech boss.'},
  {id:'exit_23', name:'Exit 23, The Ghost Ramp', color:'#9adfff', skin:'arrow', archetype:'rocketeer', hp:1160, r:44, speed:1.34, desc:'Impossible highway boss.'},
  {id:'black_entity', name:'The Black Entity', color:'#101820', skin:'blackstar', archetype:'shadow', hp:1180, r:45, speed:1.42, desc:'Anomaly boss.'},
  {id:'remembrance_core', name:'The Remembrance Core', color:'#7fa0ff', skin:'savefile', archetype:'spark', hp:1240, r:46, speed:1.08, desc:'Broken VN/save boss.'}
];
function fragCountsForMode(mode, playerCount=2){
  const players=clamp(Math.floor(Number(playerCount)||2),1,6);
  const extra=Math.max(0,players-2);
  if(mode==='bossrush') return {xp:0,natural:0,ability:0,evo:0,world:0,cursed:0};
  if(mode==='test') return {xp:44,natural:12,ability:6,evo:4,world:0,cursed:0};
  if(mode==='br') return {xp:132+extra*8,natural:38+extra*2,ability:9+Math.min(3,extra),evo:6+Math.min(2,extra),world:1,cursed:2};
  return {
    xp:115+extra*10,
    natural:36+extra*3,
    ability:9+Math.min(3,extra),
    evo:6+Math.min(2,extra),
    world:2,
    cursed:2
  };
}
const MAX_SHARED_FRAGMENTS=340;
function trimSharedFragments(room,target=MAX_SHARED_FRAGMENTS){
  if(!room||!Array.isArray(room.fragments))return;
  const now=Date.now();
  while(room.fragments.length>target){
    let index=room.fragments.findIndex(f=>(f.kind==='xp'||f.kind==='natural')&&(!f.protectedUntil||f.protectedUntil<now));
    if(index<0)index=room.fragments.findIndex(f=>!f.protectedUntil||f.protectedUntil<now);
    if(index<0)index=0;
    room.fragments.splice(index,1);
  }
}
function reserveSharedFragmentSpace(room,count){trimSharedFragments(room,Math.max(0,MAX_SHARED_FRAGMENTS-Math.max(0,count||0)));}
function spawnSharedFragment(room, kind='xp', x=null, y=null, extra=null){
  x = x == null ? rand(-HALF_W+140, HALF_W-140) : x;
  y = y == null ? rand(-HALF_H+140, HALF_H-140) : y;
  const f = {id:'frag_' + (++room.lastFragmentSerial) + '_' + id(3), kind, x, y, vx:rand(-0.05,0.05), vy:rand(-0.05,0.05), r:9};
  if(kind === 'xp'){
    const roll = Math.random();
    f.rarityIndex = roll < .72 ? 0 : roll < .90 ? 1 : roll < .98 ? 2 : 3;
    f.r = 8 + f.rarityIndex;
  }else if(kind === 'natural'){
    f.r = 9; f.color = '#84d66e';
  }else if(kind === 'ability'){
    f.ability = extra || abilityIds[irand(0, abilityIds.length)]; f.r=11;
  }else if(kind === 'evo'){
    f.core = extra || (Math.random()<0.66 ? coreIds[irand(8,coreIds.length)] : coreIds[irand(0,8)]); f.r=12;
  }else if(kind === 'world'){
    f.mode = extra || worldDefs[irand(0, worldDefs.length)]; f.r=12;
  }else if(kind === 'cursed'){
    f.curse = extra || ['glass','greed','speed','boss'][irand(0,4)]; f.r=13;
  }
  room.fragments.push(f);
  return f;
}
function fragmentSnapshot(f){
  return {
    id:f.id, kind:f.kind, x:Math.round(f.x*10)/10, y:Math.round(f.y*10)/10,
    vx:Math.round((f.vx||0)*100)/100, vy:Math.round((f.vy||0)*100)/100, r:f.r,
    rarityIndex:f.rarityIndex, ability:f.ability, core:f.core, mode:f.mode, curse:f.curse, color:f.color
  };
}
function broadcastFragmentBatch(room, spawned, reason='drop'){
  if(!room || !Array.isArray(spawned) || !spawned.length) return;
  broadcast(room.code,{
    type:'fragment_spawn_batch',
    reason,
    fragments:spawned.map(fragmentSnapshot)
  });
}
function spawnDeathFragmentBurst(room, x, y, count, reason='death', abilityChance=0){
  const spawned=[];
  const safeCount=clamp(Math.floor(Number(count)||0),0,60);
  reserveSharedFragmentSpace(room,safeCount+1);
  for(let i=0;i<safeCount;i++){
    const a=rand(0,Math.PI*2);
    const radius=Math.sqrt(Math.random())*rand(38,115);
    const kind=i>0 && i%8===0 ? 'natural' : 'xp';
    const fragment=spawnSharedFragment(room,kind,x+Math.cos(a)*radius,y+Math.sin(a)*radius);fragment.protectedUntil=Date.now()+9000;spawned.push(fragment);
  }
  if(abilityChance>0 && Math.random()<abilityChance){
    const abilityFragment=spawnSharedFragment(room,'ability',x+rand(-55,55),y+rand(-55,55));abilityFragment.protectedUntil=Date.now()+12000;spawned.push(abilityFragment);
  }
  broadcastFragmentBatch(room,spawned,reason);
  return spawned;
}
function initSharedFragments(room){
  room.fragments = [];
  const counts = fragCountsForMode(room.mode, room.clients.size);
  for(const [kind,count] of Object.entries(counts)) for(let i=0;i<count;i++) spawnSharedFragment(room, kind);
}
function initSharedWorld(room){
  initSharedFragments(room);
  room.bosses = [];
  room.terrainFeatures = [];
  room.hotZone = null;
  room.nextTerrainAt = Date.now()+rand(4500,9000);
  room.nextHotZoneAt = Date.now()+rand(15000,26000);
  room.world = {mode:null, timer:0, zones:[], nextAt:Date.now()+rand(26000,42000)};
  room.nextBossAt = ['test','br','bossrush'].includes(room.mode) ? 9999999999999 : Date.now()+rand(24000,36000);
}
function maybeRefillFragments(room){
  if(!room.matchStarted || room.mode==='bossrush') return;
  const now=Date.now();
  if(now<(room.nextFragmentRefillAt||0)) return;
  room.nextFragmentRefillAt=now+220;

  const counts={xp:0,natural:0,ability:0,evo:0,world:0,cursed:0};
  for(const f of room.fragments) counts[f.kind]=(counts[f.kind]||0)+1;
  const want=fragCountsForMode(room.mode,room.clients.size);

  let budget=3;
  const spawnIfMissing=(kind, condition=true)=>{
    if(budget<=0 || !condition || counts[kind]>=want[kind]) return false;
    spawnSharedFragment(room,kind);
    counts[kind]++;
    budget--;
    return true;
  };

  while(budget>0){
    const deficits=Object.keys(want)
      .filter(kind=>want[kind]>0 && counts[kind]<want[kind])
      .sort((a,b)=>(want[b]-counts[b])-(want[a]-counts[a]));
    if(!deficits.length) break;
    const kind=deficits[0];
    if(kind==='world' && room.world.mode){ counts.world=want.world; continue; }
    if(!spawnIfMissing(kind)) break;
  }

  trimSharedFragments(room,MAX_SHARED_FRAGMENTS);
}
function activateSharedWorld(room, modeObj=null){
  const def = modeObj?.key ? (worldDefs.find(w=>w.key===modeObj.key) || modeObj) : worldDefs[irand(0, worldDefs.length)];
  room.world.mode = def;
  room.world.timer = 90000;
  room.world.zones = [];
  const count = def.key === 'golden' ? 4 : 6;
  for(let i=0;i<count;i++){
    room.world.zones.push({id:'zone_'+id(4), kind:def.key, x:rand(-HALF_W+520,HALF_W-520), y:rand(-HALF_H+520,HALF_H-520), r:rand(210,380), life:room.world.timer});
  }
  broadcast(room.code, {type:'world_event', action:'activate', world:def, timer:room.world.timer, zones:room.world.zones});
}
function worldSnapshot(room){
  return {
    mode:room.world.mode,
    timer:Math.max(0, Math.round(room.world.timer)),
    zones:room.world.zones.map(z=>({id:z.id, kind:z.kind, x:Math.round(z.x*10)/10, y:Math.round(z.y*10)/10, r:Math.round(z.r), life:Math.max(0, Math.round(z.life))})),
    terrain:room.terrainFeatures.map(terrainSnapshot),
    hotZone:hotZoneSnapshot(room.hotZone)
  };
}
function spawnSharedBoss(room, forcedId=null){
  if(['test','br','bossrush'].includes(room.mode)) return null;
  if(room.bosses.some(b=>!b.dead)) return null;
  const def = forcedId ? (bossDefs.find(b=>b.id===forcedId) || bossDefs[0]) : bossDefs[irand(0,bossDefs.length)];
  const b = {
    id:'boss_' + (++room.lastBossSerial) + '_' + id(3), bossKind:def.id, name:def.name, color:def.color, skin:def.skin, archetype:def.archetype,
    x:rand(-HALF_W+900,HALF_W-900), y:rand(-HALF_H+700,HALF_H-700), vx:0, vy:0, r:def.r, hp:def.hp, maxHp:def.hp, speed:def.speed,
    angle:rand(0,Math.PI*2), dead:false, fireCd:1.2, desc:def.desc
  };
  room.bosses.push(b);
  broadcast(room.code, {type:'boss_event', action:'spawn', boss:bossSnapshot(b)});
  return b;
}
function bossSnapshot(b){
  return {id:b.id, bossKind:b.bossKind, name:b.name, x:Math.round(b.x*10)/10, y:Math.round(b.y*10)/10, vx:Math.round(b.vx*100)/100, vy:Math.round(b.vy*100)/100, r:b.r, angle:b.angle, hp:Math.max(0,Math.round(b.hp*10)/10), maxHp:b.maxHp, color:b.color, skin:b.skin, archetype:b.archetype, dead:!!b.dead, desc:b.desc};
}
function nearestTargetForBoss(room, boss){
  let best=null, bestD=Infinity;
  for(const snap of livePlayerSnapshots(room)){
    if(clientIsInvincible(snap.client)) continue;
    const d=Math.hypot((snap.x||0)-boss.x,(snap.y||0)-boss.y);
    if(d<bestD){bestD=d; best=snap;}
  }
  return best ? {snap:best,d:bestD} : null;
}
function updateSharedBosses(room, dt){
  if(!room.matchStarted || ['test','br','bossrush'].includes(room.mode)) return;
  const now=Date.now();
  if(now > room.nextBossAt){ spawnSharedBoss(room); room.nextBossAt=now+rand(70000,100000); }
  for(const b of room.bosses){
    if(b.dead) continue;
    const target=nearestTargetForBoss(room,b);
    if(target){
      const snap=target.snap;
      b.angle=Math.atan2((snap.y||0)-b.y,(snap.x||0)-b.x);
      const d=target.d;
      const tx=Math.cos(b.angle), ty=Math.sin(b.angle);
      const desired=430;
      let mx=0,my=0;
      if(d>desired+80){mx=tx;my=ty;}
      else if(d<desired-120){mx=-tx;my=-ty;}
      else{mx=-Math.sin(b.angle)*.75;my=Math.cos(b.angle)*.75;}
      b.vx=b.vx*.90+mx*b.speed*.10;
      b.vy=b.vy*.90+my*b.speed*.10;
      b.fireCd-=dt/1000;
      if(b.fireCd<=0 && d<760){
        b.fireCd=rand(.72,1.35);
        const shot={kind:'boss',speed:5.2,life:135,dmg:13,color:b.color,size:9,visualOnly:true,networkReplay:true};
        broadcast(room.code,{type:'boss_projectile',bossId:b.id,boss:bossSnapshot(b),angle:b.angle+rand(-.16,.16),options:shot});
        if(d<650 && Math.random()<.42){
          sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount:shot.dmg});
        }
      }
    }else{
      b.vx*=.92; b.vy*=.92;
    }
    b.x=clamp(b.x+b.vx*dt/16.6,-HALF_W+80,HALF_W-80);
    b.y=clamp(b.y+b.vy*dt/16.6,-HALF_H+80,HALF_H-80);
  }
  room.bosses=room.bosses.filter(b=>!b.removeAt||Date.now()<b.removeAt);
}
function updateSharedWorld(room, dt){
  if(!room.matchStarted || room.mode === 'bossrush') return;
  const now=Date.now();
  updateSharedMapSystems(room, dt);
  maybeRefillFragments(room);
  for(const f of room.fragments){ f.x=clamp(f.x+(f.vx||0)*dt/16.6,-HALF_W+20,HALF_W-20); f.y=clamp(f.y+(f.vy||0)*dt/16.6,-HALF_H+20,HALF_H-20); }
  if(room.world.mode){
    room.world.timer=Math.max(0, room.world.timer-dt);
    for(const z of room.world.zones) z.life=Math.max(0, z.life-dt);
    if(room.world.timer<=0){
      room.world.mode=null; room.world.zones=[]; room.world.nextAt=now+rand(42000,68000);
      broadcast(room.code, {type:'world_event', action:'clear'});
    }else if(room.world.mode.key==='golden' && Math.random()<.06){ spawnSharedFragment(room, Math.random()<.78?'xp':'natural', rand(-HALF_W+220,HALF_W-220), rand(-HALF_H+220,HALF_H-220)); }
    else if(room.world.mode.key==='overgrowth' && Math.random()<.05){ spawnSharedFragment(room, 'natural', rand(-HALF_W+220,HALF_W-220), rand(-HALF_H+220,HALF_H-220)); }
  }else if(now > room.world.nextAt && !['test','br'].includes(room.mode)){
    activateSharedWorld(room);
  }
}
function sendSharedState(client, room, immediate=false){
  send(client, {type:'fragments_state', fragments:room.fragments.map(fragmentSnapshot), immediate});
  send(client, {type:'world_state', world:worldSnapshot(room), immediate});
  send(client, {type:'bosses_state', bosses:room.bosses.map(bossSnapshot), immediate});
}
function broadcastSharedState(room, immediate=false){
  broadcast(room.code, {type:'fragments_state', fragments:room.fragments.map(fragmentSnapshot), immediate});
  broadcast(room.code, {type:'world_state', world:worldSnapshot(room), immediate});
  broadcast(room.code, {type:'bosses_state', bosses:room.bosses.map(bossSnapshot), immediate});
}
function updateSharedBroadcasts(room){
  const now=Date.now();
  if(now-room.lastFragmentBroadcast>700){ room.lastFragmentBroadcast=now; broadcast(room.code, {type:'fragments_state', fragments:room.fragments.map(fragmentSnapshot)}); }
  if(now-room.lastWorldBroadcast>1200){ room.lastWorldBroadcast=now; broadcast(room.code, {type:'world_state', world:worldSnapshot(room)}); }
  if(now-room.lastBossBroadcast>120){ room.lastBossBroadcast=now; broadcast(room.code, {type:'bosses_state', bosses:room.bosses.map(bossSnapshot)}); }
}
function collectSharedFragment(room, client, fid){
  const idx=room.fragments.findIndex(f=>f.id===fid);
  if(idx<0) return;
  const f=room.fragments[idx];
  const snap=client.snapshot || {};
  if(Math.hypot((snap.x||0)-f.x,(snap.y||0)-f.y)>140) return;
  room.fragments.splice(idx,1);
  if(f.kind==='world') activateSharedWorld(room, f.mode);
  send(client, {type:'fragment_reward', fragment:fragmentSnapshot(f)});
  broadcast(room.code, {type:'fragment_collected', id:f.id, by:client.id}, null);
}

function normalizeTargetRef(room, sourceClient, rawRef){
  const ref=String(rawRef||'').slice(0,96);
  const m=/^(player|bot|boss):([a-zA-Z0-9_\-]+)$/.exec(ref);
  if(!m) return '';
  const [,kind,targetId]=m;
  if(kind==='player'){
    const target=getClientById(room,targetId);
    if(!target || target===sourceClient || !target.snapshot || target.snapshot.dead) return '';
    if(sameCombatTeam(sourceClient.serverTeam,target.serverTeam)) return '';
    return 'player:'+targetId;
  }
  if(kind==='bot'){
    const target=room.bots.find(b=>b.id===targetId && !b.dead);
    if(!target || sameCombatTeam(sourceClient.serverTeam,target.team)) return '';
    return 'bot:'+targetId;
  }
  const boss=room.bosses.find(b=>b.id===targetId && !b.dead);
  return boss ? 'boss:'+targetId : '';
}
function chooseHomingTargetRef(room, sourceClient){
  const owner=sourceClient.snapshot;
  if(!owner) return '';
  let best='',bestD=Infinity;
  for(const target of room.clients){
    if(target===sourceClient || !target.snapshot || target.snapshot.dead || clientIsInvincible(target)) continue;
    if(finiteNumber(target.snapshot.invisible,0,0,30)>0.03) continue;
    if(sameCombatTeam(sourceClient.serverTeam,target.serverTeam)) continue;
    const d=Math.hypot((target.snapshot.x||0)-(owner.x||0),(target.snapshot.y||0)-(owner.y||0));
    if(d<bestD){bestD=d;best='player:'+target.id;}
  }
  for(const bot of room.bots){
    if(bot.dead || sameCombatTeam(sourceClient.serverTeam,bot.team)) continue;
    const d=Math.hypot(bot.x-(owner.x||0),bot.y-(owner.y||0));
    if(d<bestD){bestD=d;best='bot:'+bot.id;}
  }
  for(const boss of room.bosses){
    if(boss.dead) continue;
    const d=Math.hypot(boss.x-(owner.x||0),boss.y-(owner.y||0));
    if(d<bestD){bestD=d;best='boss:'+boss.id;}
  }
  return best;
}
function sanitizeProjectileOptions(room, client, raw){
  const out={};
  if(raw && typeof raw==='object'){
    let count=0;
    for(const [key,value] of Object.entries(raw)){
      if(count++>64 || ['owner','hitIds'].includes(key)) continue;
      if(typeof value==='number' && Number.isFinite(value)){
        const debugAuthorized=developerDebugSnapshotAuthorized(client);
        const damageLike=['damage','dmg','tickDamage','explosionDamage'].includes(key);
        const limit=damageLike?(debugAuthorized?5000:450):100000;
        out[key]=clamp(value,-limit,limit);
      }
      else if(typeof value==='boolean') out[key]=value;
      else if(typeof value==='string') out[key]=value.slice(0,96);
    }
  }
  out.kind=safeToken(out.kind||'basic',32)||'basic';
  out.networkTargetRef=normalizeTargetRef(room,client,out.networkTargetRef);
  if(!out.networkTargetRef && (out.homing || out.guided || ['homing','hive','gravity','poison'].includes(out.kind))){
    out.networkTargetRef=chooseHomingTargetRef(room,client);
  }
  return out;
}

function joinClientToRoom(client, room, options={}){
  const requestedMatchTeam=options.matchTeam==='blue'||options.matchTeam==='red'?options.matchTeam:null;
  removeFromRoom(client,{keepSnapshot:false});
  if(requestedMatchTeam) client.matchTeam=requestedMatchTeam;
  client.room=room.code;
  client.role='player';
  client.name=safeName(options.name||client.profile?.username||client.name||'Player');
  client.mode=cleanMode(options.mode||room.mode);
  client.ready=false;
  client.inMatch=!!room.matchStarted;
  client.snapshot=null;
  client.spawnProtectedUntil=Date.now()+3000;
  room.emptySince=0;
  room.clients.add(client);
  chooseLeader(room);
  assignRoomTeams(room);
  send(client,{type:'welcome',clientId:client.id,room:room.code,hidden:true});
  const peers=peersFor(client);
  if(peers.length) send(client,{type:'peers',peers});
  broadcast(room.code,{type:'peer_joined',clientId:client.id,name:client.name,mode:room.mode},client);
  broadcastLobby(room);
  if(room.matchStarted){
    client.inMatch=true;
    const near=options.spawnNearClient?.snapshot ? {x:options.spawnNearClient.snapshot.x||0,y:options.spawnNearClient.snapshot.y||0} : null;
    send(client,{type:'match_start',mode:room.mode,matchId:room.matchId,startedAt:room.startedAt||Date.now(),lateJoin:true,quickPlayBackfill:!!options.quickPlayBackfill,spawnNear:near,playerCards:roomPlayerCards(room)});
    send(client,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)});
    sendSharedState(client,room,true);
    if(room.mode!=='br') reconcileServerBots(room);
  }
  broadcastPresenceForUser(client.userId);
}

async function supabaseRequest(endpoint, token, options={}){
  const base=String(process.env.SUPABASE_URL||'').replace(/\/+$/,'');
  const key=String(process.env.SUPABASE_PUBLISHABLE_KEY||'').trim();
  if(!base || !key) throw new Error('Supabase server variables are missing.');
  const headers={apikey:key,Authorization:'Bearer '+token,'Content-Type':'application/json',...(options.headers||{})};
  const response=await fetch(base+endpoint,{...options,headers});
  let body=null;
  try{ body=await response.json(); }catch(_e){}
  if(!response.ok) throw new Error(body?.message||body?.msg||body?.error_description||('Supabase HTTP '+response.status));
  return body;
}

function supabaseAdminConfigured(){
  return !!(
    String(process.env.SUPABASE_URL||'').trim()
    && String(process.env.SUPABASE_SECRET_KEY||process.env.SUPABASE_SERVICE_ROLE_KEY||'').trim()
  );
}
async function supabaseAdminRequest(endpoint, options={}){
  const base=String(process.env.SUPABASE_URL||'').replace(/\/+$/,'');
  const secret=String(process.env.SUPABASE_SECRET_KEY||process.env.SUPABASE_SERVICE_ROLE_KEY||'').trim();
  if(!base || !secret) throw new Error('SUPABASE_SECRET_KEY is not configured on the Render server.');
  const headers={
    apikey:secret,
    Authorization:'Bearer '+secret,
    'Content-Type':'application/json',
    ...(options.headers||{})
  };
  const response=await fetch(base+endpoint,{...options,headers});
  let body=null;
  try{body=await response.json();}catch(_error){}
  if(!response.ok){
    throw new Error(
      body?.message
      ||body?.msg
      ||body?.error
      ||body?.error_description
      ||body?.hint
      ||('Supabase admin HTTP '+response.status)
    );
  }
  return body;
}
function safeModeratorText(value,maxLength=500){
  return String(value||'')
    .replace(/[<>]/g,'')
    .replace(/\s+/g,' ')
    .trim()
    .slice(0,maxLength);
}
function publicAccountRole(value){
  return value==='developer'?'developer':'player';
}
async function loadAccountRole(userId){
  userId=cleanUserId(userId);
  if(!userId || !supabaseAdminConfigured()) return 'player';
  try{
    const rows=await supabaseAdminRequest(
      '/rest/v1/account_roles'
      +'?user_id=eq.'+encodeURIComponent(userId)
      +'&select=role&limit=1',
      {method:'GET'}
    );
    return publicAccountRole(Array.isArray(rows)?rows[0]?.role:null);
  }catch(error){
    console.error('[Fragment.io] Account role lookup failed:',error.message||error);
    return 'player';
  }
}
function isDeveloper(client){
  return !!(
    client?.authenticated
    &&client?.userId
    &&client.accountRole==='developer'
  );
}
function requireDeveloper(client){
  if(isDeveloper(client)) return true;
  send(client,{type:'developer_error',message:'Verified Developer permission required.'});
  return false;
}
function broadcastGlobal(payload){
  for(const target of clients) send(target,payload);
}
function moderatorNotice(client,message){
  send(client,{type:'developer_notice',message:safeModeratorText(message,300)||'Action completed.'});
}
function moderatorError(client,error,fallback='Developer action failed.'){
  send(client,{type:'developer_error',message:safeModeratorText(error?.message||error||fallback,300)||fallback});
}
async function insertModerationAction({
  moderator,
  targetUserId=null,
  targetName=null,
  action,
  reason='',
  roomCode=null,
  metadata={}
}){
  if(!moderator?.userId || !action) return;
  await supabaseAdminRequest('/rest/v1/moderation_actions',{
    method:'POST',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      moderator_user_id:moderator.userId,
      moderator_name:moderator.name,
      target_user_id:targetUserId||null,
      target_name:targetName||null,
      action:safeToken(action,48),
      reason:safeModeratorText(reason,500),
      room_code:roomCode||null,
      metadata:metadata&&typeof metadata==='object'?metadata:{}
    })
  });
}
async function activeSanctionsForUser(userId){
  userId=cleanUserId(userId);
  if(!userId || !supabaseAdminConfigured()) return [];
  const rows=await supabaseAdminRequest(
    '/rest/v1/moderation_sanctions'
    +'?target_user_id=eq.'+encodeURIComponent(userId)
    +'&active=eq.true'
    +'&select=id,target_user_id,target_name,sanction_type,reason,expires_at,active,created_by,creator_name,created_at'
    +'&order=created_at.desc',
    {method:'GET'}
  );
  const now=Date.now();
  const active=[];
  for(const row of (Array.isArray(rows)?rows:[])){
    const expiry=row.expires_at?Date.parse(row.expires_at):Infinity;
    if(Number.isFinite(expiry)&&expiry<=now){
      supabaseAdminRequest('/rest/v1/moderation_sanctions?id=eq.'+encodeURIComponent(row.id),{
        method:'PATCH',
        headers:{Prefer:'return=minimal'},
        body:JSON.stringify({active:false,lifted_at:new Date().toISOString()})
      }).catch(()=>{});
      continue;
    }
    active.push(row);
  }
  return active;
}
async function refreshClientSanctions(client){
  client.moderationMutedUntil=0;
  if(!client?.userId || client.accountRole==='developer') return;
  const sanctions=await activeSanctionsForUser(client.userId);
  const ban=sanctions.find(row=>row.sanction_type==='ban');
  if(ban){
    const until=ban.expires_at?new Date(ban.expires_at).toLocaleString('en-GB',{timeZone:'UTC'})+' UTC':'further notice';
    throw new Error('This account is suspended until '+until+'. Reason: '+(ban.reason||'No reason supplied.'));
  }
  for(const row of sanctions){
    if(row.sanction_type!=='mute') continue;
    const expiry=row.expires_at?Date.parse(row.expires_at):Date.now()+3600000;
    client.moderationMutedUntil=Math.max(client.moderationMutedUntil||0,expiry);
  }
}
async function resolveTargetRole(targetUserId){
  const online=onlineClientForUser(targetUserId);
  if(online) return online.accountRole;
  return loadAccountRole(targetUserId);
}
async function ensureModeratableTarget(targetUserId){
  targetUserId=cleanUserId(targetUserId);
  if(!targetUserId) throw new Error('Invalid moderation target.');
  if(await resolveTargetRole(targetUserId)==='developer'){
    throw new Error('Verified Developer accounts cannot be moderated from this panel.');
  }
  return targetUserId;
}
function developerOnlinePlayers(){
  const result=[];
  const seen=new Set();
  for(const online of clients){
    if(!online.authenticated||!online.userId||seen.has(online.userId)) continue;
    seen.add(online.userId);
    const room=online.room?rooms.get(online.room):null;
    const sessions=allOnlineClientsForUser(online.userId);
    result.push({
      userId:online.userId,
      name:online.profile?.username||online.name||'Player',
      accountRole:publicAccountRole(online.accountRole),
      roomCode:online.room||null,
      mode:room?.mode||online.mode||null,
      inMatch:!!online.inMatch,
      status:online.role==='spectator'?'spectating':online.inMatch?'in_match':online.queueId?'searching':'online',
      connectedSessions:sessions.length,
      mutedUntil:Math.max(0,...sessions.map(session=>Number(session.moderationMutedUntil)||0))
    });
  }
  return result.sort((a,b)=>a.name.localeCompare(b.name));
}
async function developerPanelData(){
  const [reports,actions,sanctions,announcements]=await Promise.all([
    supabaseAdminRequest(
      '/rest/v1/player_reports'
      +'?select=id,reporter_user_id,reporter_name,target_user_id,target_name,reason,details,room_code,status,created_at,reviewed_at,review_note'
      +'&order=created_at.desc&limit=100',
      {method:'GET'}
    ),
    supabaseAdminRequest(
      '/rest/v1/moderation_actions'
      +'?select=id,moderator_user_id,moderator_name,target_user_id,target_name,action,reason,room_code,metadata,created_at'
      +'&order=created_at.desc&limit=100',
      {method:'GET'}
    ),
    supabaseAdminRequest(
      '/rest/v1/moderation_sanctions'
      +'?active=eq.true'
      +'&select=id,target_user_id,target_name,sanction_type,reason,expires_at,active,creator_name,created_at'
      +'&order=created_at.desc&limit=100',
      {method:'GET'}
    ),
    supabaseAdminRequest(
      '/rest/v1/global_announcements'
      +'?select=id,creator_name,message,created_at'
      +'&order=created_at.desc&limit=20',
      {method:'GET'}
    )
  ]);
  const now=Date.now();
  return {
    players:developerOnlinePlayers(),
    reports:Array.isArray(reports)?reports:[],
    actions:Array.isArray(actions)?actions:[],
    sanctions:(Array.isArray(sanctions)?sanctions:[]).filter(row=>!row.expires_at||Date.parse(row.expires_at)>now),
    announcements:Array.isArray(announcements)?announcements:[],
    generatedAt:new Date().toISOString()
  };
}
async function submitPersistentPlayerReport(client,msg){
  if(!client.authenticated||!client.userId) throw new Error('Login before reporting a player.');
  const now=Date.now();
  if(now-(client.lastReportAt||0)<15000) throw new Error('Wait 15 seconds before submitting another report.');
  const targetUserId=cleanUserId(msg.targetUserId);
  if(!targetUserId||targetUserId===client.userId) throw new Error('Invalid report target.');
  const target=onlineClientForUser(targetUserId);
  const reason=safeToken(msg.reason||'unspecified',48)||'unspecified';
  const details=safeModeratorText(msg.details,500);
  client.lastReportAt=now;
  await supabaseAdminRequest('/rest/v1/player_reports',{
    method:'POST',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      reporter_user_id:client.userId,
      reporter_name:client.profile?.username||client.name||'Player',
      target_user_id:targetUserId,
      target_name:target?.profile?.username||target?.name||safeName(msg.targetName||'Unknown'),
      reason,
      details,
      room_code:client.room||null,
      status:'open'
    })
  });
}
async function developerCreateAnnouncement(client,msg){
  if(!requireDeveloper(client)) return;
  const now=Date.now();
  if(now-(client.lastAnnouncementAt||0)<10000) throw new Error('Wait 10 seconds before sending another global announcement.');
  const message=safeModeratorText(msg.message,300);
  if(message.length<2) throw new Error('Announcement is empty.');
  client.lastAnnouncementAt=now;
  await supabaseAdminRequest('/rest/v1/global_announcements',{
    method:'POST',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      created_by:client.userId,
      creator_name:client.profile?.username||client.name||'Developer',
      message
    })
  });
  await insertModerationAction({
    moderator:client,
    action:'announcement',
    reason:message,
    roomCode:client.room||null
  });
  broadcastGlobal({
    type:'global_announcement',
    message,
    author:client.profile?.username||client.name||'Developer',
    createdAt:new Date().toISOString()
  });
  moderatorNotice(client,'Global announcement sent.');
}
async function developerWarnPlayer(client,msg){
  if(!requireDeveloper(client)) return;
  const targetUserId=await ensureModeratableTarget(msg.targetUserId);
  if(targetUserId===client.userId) throw new Error('You cannot warn yourself.');
  const sessions=allOnlineClientsForUser(targetUserId);
  if(!sessions.length) throw new Error('That player is no longer online.');
  const reason=safeModeratorText(msg.reason,240)||'Please review the game rules.';
  const target=sessions[0];
  await insertModerationAction({
    moderator:client,
    targetUserId,
    targetName:target.profile?.username||target.name,
    action:'warn',
    reason,
    roomCode:target.room||null
  });
  for(const session of sessions){
    send(session,{
      type:'moderator_warning',
      reason,
      moderator:client.profile?.username||client.name||'Developer'
    });
  }
  moderatorNotice(client,(target.profile?.username||target.name)+' was warned.');
}
async function developerKickPlayer(client,msg){
  if(!requireDeveloper(client)) return;
  const targetUserId=await ensureModeratableTarget(msg.targetUserId);
  if(targetUserId===client.userId) throw new Error('You cannot kick yourself.');
  const sessions=allOnlineClientsForUser(targetUserId);
  if(!sessions.length) throw new Error('That player is no longer online.');
  const target=sessions[0];
  const reason=safeModeratorText(msg.reason,240)||'Removed by a Developer.';
  await insertModerationAction({
    moderator:client,
    targetUserId,
    targetName:target.profile?.username||target.name,
    action:'kick',
    reason,
    roomCode:target.room||null
  });
  for(const session of sessions){
    send(session,{
      type:'moderator_kick',
      reason,
      moderator:client.profile?.username||client.name||'Developer'
    });
    setTimeout(()=>{try{session.socket.destroy();}catch(_error){}},500);
  }
  moderatorNotice(client,(target.profile?.username||target.name)+' was kicked.');
}
function allowedModerationDuration(raw,allowed,fallback){
  const value=Math.floor(Number(raw)||fallback);
  return allowed.includes(value)?value:fallback;
}
async function createSanction(client,msg,type){
  if(!requireDeveloper(client)) return;
  const targetUserId=await ensureModeratableTarget(msg.targetUserId);
  if(targetUserId===client.userId) throw new Error('You cannot moderate yourself.');
  const allowed=type==='mute'?[300,900,3600,21600]:[3600,86400,604800,2592000];
  const durationSeconds=allowedModerationDuration(msg.durationSeconds,allowed,allowed[1]);
  const expiresAt=new Date(Date.now()+durationSeconds*1000).toISOString();
  const sessions=allOnlineClientsForUser(targetUserId);
  const target=sessions[0];
  const targetName=target?.profile?.username||target?.name||safeName(msg.targetName||'Unknown');
  const reason=safeModeratorText(msg.reason,300)||(type==='mute'?'Chat moderation.':'Account suspended by a Developer.');

  await supabaseAdminRequest('/rest/v1/moderation_sanctions',{
    method:'POST',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      target_user_id:targetUserId,
      target_name:targetName,
      sanction_type:type,
      reason,
      expires_at:expiresAt,
      active:true,
      created_by:client.userId,
      creator_name:client.profile?.username||client.name||'Developer'
    })
  });
  await insertModerationAction({
    moderator:client,
    targetUserId,
    targetName,
    action:type,
    reason,
    roomCode:target?.room||null,
    metadata:{durationSeconds,expiresAt}
  });

  if(type==='mute'){
    for(const session of sessions){
      session.moderationMutedUntil=Math.max(session.moderationMutedUntil||0,Date.parse(expiresAt));
      send(session,{
        type:'moderator_mute',
        reason,
        expiresAt,
        moderator:client.profile?.username||client.name||'Developer'
      });
    }
    moderatorNotice(client,targetName+' was muted.');
    return;
  }

  for(const session of sessions){
    send(session,{
      type:'moderator_ban',
      reason,
      expiresAt,
      moderator:client.profile?.username||client.name||'Developer'
    });
    setTimeout(()=>{try{session.socket.destroy();}catch(_error){}},650);
  }
  moderatorNotice(client,targetName+' was suspended.');
}
async function developerLiftSanction(client,msg){
  if(!requireDeveloper(client)) return;
  const sanctionId=Math.floor(Number(msg.sanctionId));
  if(!Number.isSafeInteger(sanctionId)||sanctionId<1) throw new Error('Invalid sanction ID.');
  const rows=await supabaseAdminRequest(
    '/rest/v1/moderation_sanctions?id=eq.'+encodeURIComponent(sanctionId)
    +'&active=eq.true'
    +'&select=id,target_user_id,target_name,sanction_type,reason&limit=1',
    {method:'GET'}
  );
  const sanction=Array.isArray(rows)?rows[0]:null;
  if(!sanction) throw new Error('That sanction is no longer active.');
  await supabaseAdminRequest('/rest/v1/moderation_sanctions?id=eq.'+encodeURIComponent(sanctionId),{
    method:'PATCH',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      active:false,
      lifted_at:new Date().toISOString(),
      lifted_by:client.userId
    })
  });
  if(sanction.sanction_type==='mute'){
    for(const session of allOnlineClientsForUser(sanction.target_user_id)){
      const remaining=await activeSanctionsForUser(sanction.target_user_id);
      session.moderationMutedUntil=Math.max(0,...remaining.filter(row=>row.sanction_type==='mute').map(row=>Date.parse(row.expires_at)||0));
      send(session,{type:'moderator_unmute'});
    }
  }
  await insertModerationAction({
    moderator:client,
    targetUserId:sanction.target_user_id,
    targetName:sanction.target_name,
    action:sanction.sanction_type==='ban'?'unban':'unmute',
    reason:safeModeratorText(msg.reason,240)||'Sanction lifted.',
    metadata:{sanctionId}
  });
  moderatorNotice(client,'Sanction lifted for '+(sanction.target_name||'player')+'.');
}
async function developerUpdateReport(client,msg){
  if(!requireDeveloper(client)) return;
  const reportId=Math.floor(Number(msg.reportId));
  const status=String(msg.status||'');
  if(!Number.isSafeInteger(reportId)||reportId<1) throw new Error('Invalid report ID.');
  if(!['reviewing','resolved','dismissed'].includes(status)) throw new Error('Invalid report status.');
  const reviewNote=safeModeratorText(msg.reviewNote,500);
  await supabaseAdminRequest('/rest/v1/player_reports?id=eq.'+encodeURIComponent(reportId),{
    method:'PATCH',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      status,
      reviewed_by:client.userId,
      review_note:reviewNote,
      reviewed_at:new Date().toISOString()
    })
  });
  await insertModerationAction({
    moderator:client,
    action:'report_'+status,
    reason:reviewNote,
    metadata:{reportId}
  });
  moderatorNotice(client,'Report #'+reportId+' marked '+status+'.');
}


const DEVELOPER_DEBUG_EVOLUTIONS=new Set([
  'starter','double','triple','hydra','sniper','marksman','deadeye',
  'devourer','gluttony','world_eater','boomerang','orbiter','planetary',
  'rocketeer','destroyer','warhead','machine','minigunner','bullet_storm',
  'swordsman','samurai','ronin','cloner','doppelgaenger','hakka',
  'kindler','hellflame','azure','laser','laser_cannon','solar_lance',
  'drone','swarm_master','hive_mind','spark','stormcaller','thunder_god',
  'shadow','phantom','nightmare','gravity_mage','singularity','black_star',
  'parasite','leech_king','bloodlord','selfburn','matter_reaper',
  'black_hole','blood_spark','voidblade','rocket_swarm','railgunner',
  'storm_core','root_admin'
]);
const DEVELOPER_DEBUG_VARIANTS=new Set([
  'hydra','deadeye','world_eater','planetary','warhead','bullet_storm',
  'ronin','hakka','azure','solar_lance','hive_mind','thunder_god',
  'nightmare','black_star','bloodlord','selfburn'
]);
const DEVELOPER_DEBUG_FRAGMENTS=new Set([
  'mirror','void','titan','glass','gravity','blood','frost','memory',
  'echo','swift','reach','ember'
]);
const DEVELOPER_DEBUG_ABILITIES=new Set([
  'bullet_spam','freeze_ray','gravity_bullet','precision_strike','flare',
  'magnet','knockback','poison_dart','ricochet_dart','super_speed',
  'fragment_mine','reflect_shield','loot_radar','swap_position','wall_drop',
  'judgement_laser','fake_death','copycat','bullet_eater','fragment_storm'
]);
const DEVELOPER_DEBUG_WORLDS=Object.freeze({
  blood:{key:'blood',name:'Blood Moon',color:'#a84343',desc:'Red blood zones bleed fighters and reward risky close combat.'},
  frozen:{key:'frozen',name:'Frozen World',color:'#6ca7d8',desc:'Ice fields form around the map and heavily slow anyone inside.'},
  storm:{key:'storm',name:'Storm Front',color:'#5f6f8f',desc:'Warning circles appear before lightning strikes and static fields.'},
  overgrowth:{key:'overgrowth',name:'Overgrowth',color:'#4d9460',desc:'Vine gardens slow movement but grow natural fragments.'},
  zero:{key:'zero',name:'Zero Gravity',color:'#8e86cf',desc:'Gravity bubbles make movement floaty and bend projectiles.'},
  eclipse:{key:'eclipse',name:'Lunar Eclipse',color:'#27334f',desc:'Dark eclipse zones hide movement and punish careless chases.'},
  meteor:{key:'meteor',name:'Meteor Shower',color:'#bd6b43',desc:'Meteors show warning circles before impact, leaving burning loot zones.'},
  corruption:{key:'corruption',name:'Corruption Bloom',color:'#70429c',desc:'Void blooms drain health but can crystallize into rare fragments.'},
  golden:{key:'golden',name:'Golden Rain',color:'#d6a84a',desc:'Golden showers create safe loot zones and bonus fragments.'}
});
const DEVELOPER_DEBUG_SESSION_MS=10*60*1000;
const DEVELOPER_DEBUG_ACTION_GAP_MS=90;

function developerDebugScope(client){
  if(!isDeveloper(client)) return null;

  if(!client.room){
    return {kind:'offline',roomCode:null,mode:'offline'};
  }

  const room=rooms.get(client.room);
  if(!room||!client.inMatch||!room.matchStarted){
    return null;
  }

  return {
    kind:'active_game',
    roomCode:room.code,
    mode:room.mode
  };
}

function developerDebugSessionValid(client,token=null){
  const session=client?.developerDebugSession;
  if(!session||!isDeveloper(client)) return false;
  if(Date.now()>=Number(session.expiresAt||0)) return false;
  if(token!==null&&!crypto.timingSafeEqual(
    Buffer.from(String(session.token||'')),
    Buffer.from(String(token||'').padEnd(String(session.token||'').length,'\0').slice(0,String(session.token||'').length))
  )) return false;

  const currentScope=developerDebugScope(client);
  if(!currentScope) return false;
  if(currentScope.kind!==session.scope) return false;
  if((currentScope.roomCode||null)!==(session.roomCode||null)) return false;
  return true;
}

function developerDebugSnapshotAuthorized(client){
  return developerDebugSessionValid(client,null);
}

function revokeDeveloperDebug(client,notify=true){
  if(!client) return;
  client.developerDebugSession=null;
  client.developerDebugRootAdminUntil=0;
  if(notify&&isDeveloper(client)){
    send(client,{type:'developer_debug_revoked'});
  }
}

async function openDeveloperDebugSession(client){
  // Deliberately silent for ordinary players so the hidden tool is not disclosed.
  if(!isDeveloper(client)) return;

  const scope=developerDebugScope(client);
  if(!scope){
    send(client,{
      type:'developer_debug_unavailable',
      message:'Deploy into a match before opening the Debug tool.'
    });
    return;
  }

  const token=crypto.randomBytes(24).toString('base64url');
  const expiresAt=Date.now()+DEVELOPER_DEBUG_SESSION_MS;
  client.developerDebugSession={
    token,
    scope:scope.kind,
    roomCode:scope.roomCode,
    expiresAt,
    lastActionAt:0
  };

  send(client,{
    type:'developer_debug_granted',
    token,
    scope:scope.kind,
    roomCode:scope.roomCode,
    expiresAt
  });

  insertModerationAction({
    moderator:client,
    action:'debug',
    reason:'Opened server-validated Developer Debug.',
    roomCode:scope.roomCode,
    metadata:{event:'open',scope:scope.kind,expiresAt:new Date(expiresAt).toISOString()}
  }).catch(error=>console.error('[Fragment.io] Debug audit log failed:',error.message||error));
}

function normalizeDeveloperDebugPayload(action,payload){
  payload=payload&&typeof payload==='object'?payload:{};

  if(action==='set_evolution'){
    const type=safeToken(payload.type,48);
    if(!DEVELOPER_DEBUG_EVOLUTIONS.has(type)) throw new Error('Invalid evolution.');
    return {type};
  }

  if(action==='set_variant'){
    const type=safeToken(payload.type,48);
    const fragment=safeToken(payload.fragment,48);
    if(!DEVELOPER_DEBUG_VARIANTS.has(type)||!DEVELOPER_DEBUG_FRAGMENTS.has(fragment)){
      throw new Error('Invalid sidegrade.');
    }
    if(['echo','swift','reach','ember'].includes(fragment)){
      throw new Error('A major fragment is required.');
    }
    return {type,fragment};
  }

  if(action==='give_fragment'){
    const id=safeToken(payload.id,48);
    if(!DEVELOPER_DEBUG_FRAGMENTS.has(id)) throw new Error('Invalid fragment.');
    return {id};
  }

  if(action==='give_ability'){
    const id=safeToken(payload.id,48);
    if(!DEVELOPER_DEBUG_ABILITIES.has(id)) throw new Error('Invalid ability.');
    return {id};
  }

  if(action==='force_world'){
    const key=safeToken(payload.key,48);
    if(!DEVELOPER_DEBUG_WORLDS[key]) throw new Error('Invalid world change.');
    return {key};
  }

  throw new Error('Invalid debug action.');
}

async function executeDeveloperDebugAction(client,msg){
  // Deliberately silent for ordinary players.
  if(!isDeveloper(client)) return;

  const session=client.developerDebugSession;
  if(!developerDebugSessionValid(client,msg.token)){
    revokeDeveloperDebug(client,true);
    return;
  }

  const now=Date.now();
  if(now-Number(session.lastActionAt||0)<DEVELOPER_DEBUG_ACTION_GAP_MS){
    return;
  }
  session.lastActionAt=now;

  const requestId=safeToken(msg.requestId,64);
  const action=safeToken(msg.action,48);
  if(!requestId||!action) return;

  let payload;
  try{
    payload=normalizeDeveloperDebugPayload(action,msg.payload);
  }catch(error){
    send(client,{type:'developer_debug_action_rejected',requestId});
    return;
  }

  if(action==='force_world'&&session.roomCode){
    const room=rooms.get(session.roomCode);
    if(!room||!developerDebugSessionValid(client,msg.token)){
      revokeDeveloperDebug(client,true);
      return;
    }
    activateSharedWorld(room,DEVELOPER_DEBUG_WORLDS[payload.key]);
    send(client,{type:'developer_debug_action_ok',requestId,action,scope:session.scope});
  }else{
    send(client,{
      type:'developer_debug_apply',
      requestId,
      action,
      payload,
      scope:session.scope
    });
  }

  if(action==='set_evolution'&&payload.type==='root_admin'){
    client.developerDebugRootAdminUntil=Math.min(session.expiresAt,Date.now()+5*60*1000);
  }

  insertModerationAction({
    moderator:client,
    action:'debug',
    reason:'Developer Debug action: '+action,
    roomCode:session.roomCode,
    metadata:{event:'action',scope:session.scope,action,payload}
  }).catch(error=>console.error('[Fragment.io] Debug audit log failed:',error.message||error));
}

async function refreshClientProfile(client){
  if(!client?.authenticated || client.isGuest || !client.accessToken || !client.userId) return;
  const rows=await supabaseRequest('/rest/v1/profiles?id=eq.'+encodeURIComponent(client.userId)+'&select=id,username,friend_code,about_me,equipped_title,profile_banner,profile_icon,featured_cosmetics,featured_achievements,profile_settings',client.accessToken,{method:'GET'});
  if(Array.isArray(rows) && rows[0]){
    client.profile=rows[0];
    client.name=safeName(rows[0].username||client.name||'Player');
  }
  try{
    const progressRows=await supabaseRequest('/rest/v1/player_progress?user_id=eq.'+encodeURIComponent(client.userId)+'&select=account_level,achievement_points,stats,showcased_achievements',client.accessToken,{method:'GET'});
    client.progress=Array.isArray(progressRows)?progressRows[0]||null:null;
  }catch(_error){ client.progress=null; }
}
function guestUserIdFromToken(value){
  let token=String(value||'').trim().replace(/[^a-zA-Z0-9_-]/g,'').slice(0,96);
  if(token.length<16)token=crypto.randomBytes(24).toString('hex');
  const chars=crypto.createHash('sha256').update('fragment.io guest '+token).digest('hex').slice(0,32).split('');
  chars[12]='4';
  chars[16]=['8','9','a','b'][parseInt(chars[16],16)%4];
  const raw=chars.join('');
  return raw.slice(0,8)+'-'+raw.slice(8,12)+'-'+raw.slice(12,16)+'-'+raw.slice(16,20)+'-'+raw.slice(20,32);
}
function authenticateGuestSocket(client,msg={}){
  if(client.authenticated&&client.userId){
    send(client,{type:'auth_ok',userId:client.userId,clientId:client.id,name:client.name,accountRole:publicAccountRole(client.accountRole),guest:!!client.isGuest});
    return;
  }
  const userId=guestUserIdFromToken(msg.guestToken);
  client.accessToken='';
  client.userId=userId;
  client.authenticated=true;
  client.isGuest=true;
  client.accountRole='player';
  client.name=safeName(msg.name||'Unnamed');
  client.profile={
    id:userId,
    username:client.name,
    friend_code:'',
    profile_settings:{show_status:'everyone',allow_join:'everyone',allow_spectate:'everyone'}
  };
  client.progress={account_level:1,achievement_points:0,stats:{}};
  client.friendIds=new Set();
  if(!userClients.has(userId))userClients.set(userId,new Set());
  userClients.get(userId).add(client);
  for(const party of parties.values()){
    if(party.members.has(userId)){client.partyId=party.id;break;}
  }
  send(client,{type:'auth_ok',userId,clientId:client.id,name:client.name,accountRole:'player',guest:true});
  sendPartyStateForClient(client);
  sendWatchedPresence(client);
  const reservation=reconnectReservations.get(userId);
  if(reservation&&reservation.expires>Date.now()){
    const room=rooms.get(reservation.roomCode);
    if(room){
      reconnectReservations.delete(userId);
      joinClientToRoom(client,room,{mode:room.mode,name:client.name});
      send(client,{type:'reconnect_match',mode:room.mode,room:room.code});
    }
  }
  broadcastPresenceForUser(userId);
}
async function authenticateSocket(client, token){
  token=String(token||'').trim();
  if(!token) throw new Error('Missing account token.');
  const user=await supabaseRequest('/auth/v1/user',token,{method:'GET'});
  if(!user?.id) throw new Error('Invalid account session.');
  client.accessToken=token;
  client.userId=user.id;
  client.authenticated=true;
  client.isGuest=false;
  client.accountRole=await loadAccountRole(user.id);
  client.name=safeName(user.user_metadata?.username||client.name||'Player');
  client.profile={id:user.id,username:client.name,friend_code:'',profile_settings:{}};
  try{ await refreshClientProfile(client); }catch(_e){}
  try{
    await refreshClientSanctions(client);
  }catch(error){
    client.authenticated=false;
    client.accessToken='';
    client.userId=null;
    client.accountRole='player';
    client.profile=null;
    client.progress=null;
    throw error;
  }
  if(!userClients.has(user.id)) userClients.set(user.id,new Set());
  userClients.get(user.id).add(client);
  await refreshClientFriends(client);
  for(const party of parties.values()){
    if(party.members.has(user.id)){ client.partyId=party.id; break; }
  }
  send(client,{type:'auth_ok',userId:user.id,clientId:client.id,name:client.name,accountRole:publicAccountRole(client.accountRole)});
  try{await sendFriendRequestState(client);}catch(error){console.error('[Fragment.io] Friend request state failed:',error.message||error);}
  sendPartyStateForClient(client);
  sendWatchedPresence(client);
  const reservation=reconnectReservations.get(user.id);
  if(reservation && reservation.expires>Date.now()){
    const room=rooms.get(reservation.roomCode);
    if(room){
      reconnectReservations.delete(user.id);
      joinClientToRoom(client,room,{mode:room.mode,name:client.name});
      send(client,{type:'reconnect_match',mode:room.mode,room:room.code});
    }
  }
  broadcastPresenceForUser(user.id);
}
async function refreshClientFriends(client){
  client.friendIds=new Set();
  if(!client.authenticated || client.isGuest || !client.accessToken) return;
  const rows=await supabaseRequest('/rest/v1/friendships?user_id=eq.'+encodeURIComponent(client.userId)+'&select=friend_id',client.accessToken,{method:'GET'});
  for(const row of (Array.isArray(rows)?rows:[])) if(row.friend_id) client.friendIds.add(row.friend_id);
}
function samePartyUsers(a,b){ return !!a?.partyId && a.partyId===b?.partyId; }
function presenceFor(viewer,target){
  if(!target) return {status:'offline'};
  const isFriend=!!viewer?.friendIds?.has(target.userId);
  const isParty=samePartyUsers(viewer,target);
  const settings=target.profile?.profile_settings||{};
  let status='online';
  const party=partyForClient(target);
  const queued=party?.queued || target.queueId;
  if(target.role==='spectator') status='spectating';
  else if(target.room && target.inMatch) status='in_match';
  else if(queued) status='searching';
  else if(party && party.members.size>1) status='in_party';
  if(!privacyAllows(settings.show_status||'friends',isFriend,isParty)) return {status:'online'};
  const room=target.room?rooms.get(target.room):null;
  const allowSpectate=room && modeRules(room.mode).spectate && privacyAllows(settings.allow_spectate||'friends',isFriend,isParty);
  const allowJoin=room && target.inMatch && roomJoinWindowOpen(room) && room.clients.size<roomCapacity(room) && privacyAllows(settings.allow_join||'friends',isFriend,isParty);
  return {
    status,
    accountRole:publicAccountRole(target.accountRole),
    mode:room?.mode||party?.mode||null,
    players:room?.clients?.size||0,
    capacity:room?roomCapacity(room):0,
    joinable:!!allowJoin,
    spectatable:!!allowSpectate,
    partySize:party?.members?.size||0
  };
}
function sendWatchedPresence(client){
  if(!client?.authenticated) return;
  const rows=[];
  for(const friendId of (client.friendIds||[])) rows.push({userId:friendId,...presenceFor(client,onlineClientForUser(friendId))});
  send(client,{type:'presence_state',friends:rows});
}
function broadcastPresenceForUser(userId){
  if(!userId) return;
  for(const client of clients){
    if(!client.authenticated) continue;
    if(client.userId===userId || client.friendIds?.has(userId)) sendWatchedPresence(client);
  }
}
function partyPayload(party){
  const members=[];
  for(const userId of party.members){
    const c=onlineClientForUser(userId);
    members.push({userId,name:c?.profile?.username||c?.name||party.memberNames.get(userId)||'Player',online:!!c,ready:!!party.ready.get(userId),leader:userId===party.leaderId,status:c?presenceFor(c,c).status:'offline',accountRole:publicAccountRole(c?.accountRole)});
  }
  return {type:'party_state',partyId:party.id,leaderId:party.leaderId,mode:party.mode,fillBots:party.fillBots,queued:party.queued,members};
}
function broadcastParty(party){
  if(!party) return;
  const payload=partyPayload(party);
  for(const userId of party.members) for(const c of allOnlineClientsForUser(userId)){ c.partyId=party.id; send(c,payload); }
  for(const userId of party.members) broadcastPresenceForUser(userId);
}
function sendPartyStateForClient(client){
  const party=partyForClient(client);
  if(party) send(client,partyPayload(party));
  else send(client,{type:'party_state',partyId:null,leaderId:null,mode:'normal',fillBots:true,queued:false,members:client.authenticated?[{userId:client.userId,name:client.name,online:true,ready:false,leader:true,status:'online',accountRole:publicAccountRole(client.accountRole)}]:[]});
}
function ensureParty(client){
  let party=partyForClient(client);
  if(party) return party;
  party={id:partyCode(),leaderId:client.userId,members:new Set([client.userId]),memberNames:new Map([[client.userId,client.name]]),ready:new Map([[client.userId,false]]),mode:'normal',fillBots:true,queued:false,queueId:null,createdAt:Date.now()};
  parties.set(party.id,party); client.partyId=party.id; broadcastParty(party); return party;
}
function leavePartyUser(userId,party){
  if(!party || !party.members.has(userId)) return;
  party.members.delete(userId); party.ready.delete(userId); party.memberNames.delete(userId);
  for(const c of allOnlineClientsForUser(userId)){ c.partyId=null; sendPartyStateForClient(c); }
  if(party.leaderId===userId) party.leaderId=party.members.values().next().value||null;
  if(!party.members.size){ parties.delete(party.id); cancelQueueParty(party); }
  else broadcastParty(party);
}
function cancelQueueParty(party){
  if(!party) return;
  for(const [mode,list] of matchQueues){ matchQueues.set(mode,list.filter(entry=>entry.partyId!==party.id)); }
  party.queued=false; party.queueId=null; broadcastParty(party);
}
function queueMembersForEntry(entry){ return entry.userIds.map(onlineClientForUser).filter(c=>c&&c.authenticated&&!c.room); }
function queueEntry(client,mode,asParty=true,fillBots=true){
  mode=cleanMode(mode);
  if(mode==='test') return send(client,{type:'queue_error',message:'Test Arena is offline training only.'});
  let party=partyForClient(client);
  let userIds=[client.userId],partyId=null;
  if(asParty && party && party.members.size>1){
    if(party.leaderId!==client.userId) return send(client,{type:'queue_error',message:'Only the party leader can start matchmaking.'});
    const onlineIds=[...party.members].filter(id=>onlineClientForUser(id));
    if(onlineIds.length!==party.members.size) return send(client,{type:'queue_error',message:'Every party member must be online.'});
    if([...party.members].some(id=>id!==party.leaderId && !party.ready.get(id))) return send(client,{type:'queue_error',message:'Every party member must be ready.'});
    userIds=[...party.members]; partyId=party.id; party.mode=mode; party.fillBots=mode==='squad'&&fillBots!==false; party.queued=true;
  }
  const rules=modeRules(mode);
  if(userIds.length>rules.partyMax) return send(client,{type:'queue_error',message:'This mode allows parties of up to '+rules.partyMax+'.'});
  if(userIds.length>rules.capacity) return send(client,{type:'queue_error',message:'Party is too large for this mode.'});
  for(const list of matchQueues.values()){
    for(let i=list.length-1;i>=0;i--) if(list[i].userIds.some(id=>userIds.includes(id))) list.splice(i,1);
  }
  const entry={id:'Q-'+id(4),partyId,userIds,mode,fillBots:true,completeRoster:mode==='squad'&&fillBots!==false,queuedAt:Date.now()};
  if(tryBackfillQueueEntry(entry)) return;
  if(!matchQueues.has(mode)) matchQueues.set(mode,[]);
  matchQueues.get(mode).push(entry);
  for(const uid of userIds) for(const c of allOnlineClientsForUser(uid)){ c.queueId=entry.id; send(c,{type:'queue_state',active:true,mode,players:userIds.length,target:targetPopulationForMode(mode,userIds.length),startIn:Math.ceil(rules.waitMs/1000)}); }
  if(party) broadcastParty(party);
  for(const uid of userIds) broadcastPresenceForUser(uid);
}
function cancelClientQueue(client){
  for(const [mode,list] of matchQueues){
    const removed=list.filter(e=>e.userIds.includes(client.userId));
    matchQueues.set(mode,list.filter(e=>!e.userIds.includes(client.userId)));
    for(const e of removed){ if(e.partyId){ const p=parties.get(e.partyId); if(p){p.queued=false;p.queueId=null;broadcastParty(p);} } for(const uid of e.userIds) for(const c of allOnlineClientsForUser(uid)){c.queueId=null;send(c,{type:'queue_state',active:false});} }
  }
  broadcastPresenceForUser(client.userId);
}
function assignTeamsForEntries(room,entries){
  if(room.mode!=='teams') return;
  let blue=0,red=0;
  for(const entry of entries){
    const team=blue<=red?'blue':'red';
    for(const uid of entry.userIds){ const c=onlineClientForUser(uid); if(c) c.matchTeam=team; }
    if(team==='blue') blue+=entry.userIds.length; else red+=entry.userIds.length;
  }
}

function chooseBackfillTeam(room,groupSize){
  if(room.mode!=='teams') return null;
  const perTeam=Math.floor(roomCapacity(room)/2);
  let blue=0,red=0;
  for(const c of room.clients){
    const team=c.serverTeam||c.matchTeam;
    if(team==='blue') blue++;
    else if(team==='red') red++;
  }
  const choices=[];
  if(blue+groupSize<=perTeam) choices.push({team:'blue',count:blue});
  if(red+groupSize<=perTeam) choices.push({team:'red',count:red});
  choices.sort((a,b)=>a.count-b.count || (a.team==='blue'?-1:1));
  return choices[0]?.team||null;
}
function findOngoingBackfillRoom(mode,groupSize){
  mode=cleanMode(mode);
  if(mode==='br'||mode==='test') return null;
  const candidates=[];
  for(const room of rooms.values()){
    if(!room.matchmaking || !room.matchStarted || room.mode!==mode) continue;
    if(!roomJoinWindowOpen(room) || room.clients.size<=0) continue;
    if(room.clients.size+groupSize>roomCapacity(room)) continue;
    const team=chooseBackfillTeam(room,groupSize);
    if(mode==='teams'&&!team) continue;
    candidates.push({room,team});
  }
  candidates.sort((a,b)=>{
    const playerDiff=a.room.clients.size-b.room.clients.size;
    if(playerDiff) return playerDiff;
    const ageA=Date.now()-(a.room.startedAt||a.room.createdAt||0);
    const ageB=Date.now()-(b.room.startedAt||b.room.createdAt||0);
    if(ageA!==ageB) return ageA-ageB;
    return (a.room.lastBackfillAt||0)-(b.room.lastBackfillAt||0);
  });
  return candidates[0]||null;
}
function finishQueuedPartyEntry(entry){
  if(!entry.partyId) return;
  const party=parties.get(entry.partyId);
  if(!party) return;
  party.queued=false;
  party.queueId=null;
  for(const uid of party.members) party.ready.set(uid,false);
  broadcastParty(party);
}
function tryBackfillQueueEntry(entry){
  const members=queueMembersForEntry(entry);
  if(members.length!==entry.userIds.length) return false;
  const candidate=findOngoingBackfillRoom(entry.mode,members.length);
  if(!candidate) return false;
  const {room,team}=candidate;
  const existingPlayers=room.clients.size;
  const replacedBots=Math.min(members.length,room.bots.filter(bot=>!bot.dead).length);
  const projectedPlayers=existingPlayers+members.length;
  const elapsed=Math.max(0,Math.floor((Date.now()-(room.startedAt||Date.now()))/1000));

  for(const client of members){
    client.queueId=null;
    if(team) client.matchTeam=team;
    send(client,{type:'queue_state',active:false});
    send(client,{
      type:'match_found',mode:room.mode,players:projectedPlayers,capacity:roomCapacity(room),
      ongoing:true,backfill:true,replacedBots,elapsed
    });
  }
  for(const client of members){
    joinClientToRoom(client,room,{mode:room.mode,name:client.name,quickPlayBackfill:true,matchTeam:team});
  }
  room.lastBackfillAt=Date.now();
  finishQueuedPartyEntry(entry);
  for(const uid of entry.userIds) broadcastPresenceForUser(uid);
  return true;
}
function startQueuedMatch(mode,entries){
  const room=getRoom(matchCode());
  room.mode=mode; room.matchmaking=true; room.fillBots=true; room.completeRoster=mode==='squad'&&entries.some(e=>e.completeRoster!==false); room.matchStarted=false;
  assignTeamsForEntries(room,entries);
  for(const entry of entries){
    for(const uid of entry.userIds){
      const c=onlineClientForUser(uid);
      if(!c) continue;
      c.queueId=null;
      joinClientToRoom(c,room,{mode,name:c.name,matchTeam:c.matchTeam});
      send(c,{type:'match_found',mode,players:entries.reduce((n,e)=>n+e.userIds.length,0),capacity:roomCapacity(room)});
    }
    if(entry.partyId){ const p=parties.get(entry.partyId); if(p){p.queued=false;p.queueId=null;for(const uid of p.members)p.ready.set(uid,false);broadcastParty(p);} }
  }
  startMatch(room);
  for(const entry of entries) for(const uid of entry.userIds) broadcastPresenceForUser(uid);
}
function processMatchQueues(){
  const now=Date.now();
  for(const [mode,list] of matchQueues){
    let valid=list.filter(entry=>queueMembersForEntry(entry).length===entry.userIds.length);
    const remaining=[];
    for(const entry of valid.sort((a,b)=>a.queuedAt-b.queuedAt)){
      if(!tryBackfillQueueEntry(entry)) remaining.push(entry);
    }
    valid=remaining;
    matchQueues.set(mode,valid);
    if(!valid.length) continue;
    const rules=modeRules(mode);
    let group=[],count=0;
    for(const entry of valid){ if(count+entry.userIds.length<=rules.capacity){group.push(entry);count+=entry.userIds.length;} }
    const oldest=Math.min(...group.map(e=>e.queuedAt));
    const waited=now-oldest;
    const canStart=count>=1 && (waited>=rules.waitMs || count>=Math.min(rules.capacity,Math.max(4,rules.targetMid)));
    const startIn=Math.max(0,Math.ceil((rules.waitMs-waited)/1000));
    for(const entry of valid) for(const uid of entry.userIds) for(const c of allOnlineClientsForUser(uid)) send(c,{type:'queue_state',active:true,mode,players:count,target:targetPopulationForMode(mode,count),startIn});
    if(canStart){
      const ids=new Set(group.map(e=>e.id));
      matchQueues.set(mode,valid.filter(e=>!ids.has(e.id)));
      startQueuedMatch(mode,group);
    }
  }
}
function handlePartyInvite(client,targetUserId){
  targetUserId=cleanUserId(targetUserId);
  if(!client.authenticated || !client.friendIds?.has(targetUserId)) return send(client,{type:'social_error',message:'That account is not in your friend list.'});
  const target=onlineClientForUser(targetUserId);
  if(!target) return send(client,{type:'social_error',message:'That friend is offline.'});
  if(target.room&&target.inMatch) return send(client,{type:'social_error',message:'That friend is already in a match.'});
  const party=ensureParty(client);
  if(party.leaderId!==client.userId) return send(client,{type:'social_error',message:'Only the party leader can invite players.'});
  if(party.members.size>=6) return send(client,{type:'social_error',message:'Party is full.'});
  const inviteId='I-'+id(4);
  pendingPartyInvites.set(inviteId,{id:inviteId,partyId:party.id,fromUserId:client.userId,toUserId:targetUserId,expires:Date.now()+30000});
  send(target,{type:'party_invite',inviteId,fromUserId:client.userId,fromName:client.name,partySize:party.members.size,mode:party.mode,expiresIn:30});
  send(client,{type:'social_notice',message:'Party invite sent to '+target.name+'.'});
}
function acceptPartyInvite(client,inviteId){
  const inv=pendingPartyInvites.get(String(inviteId||''));
  if(!inv || inv.toUserId!==client.userId || inv.expires<Date.now()) return send(client,{type:'social_error',message:'That party invite expired.'});
  const party=parties.get(inv.partyId);
  if(!party || party.members.size>=6) return send(client,{type:'social_error',message:'That party is no longer available.'});
  const old=partyForClient(client); if(old&&old!==party) leavePartyUser(client.userId,old);
  party.members.add(client.userId); party.memberNames.set(client.userId,client.name); party.ready.set(client.userId,false); client.partyId=party.id;
  pendingPartyInvites.delete(inviteId); broadcastParty(party);
}
function spectateFriend(client,targetUserId){
  targetUserId=cleanUserId(targetUserId);
  if(!client.friendIds?.has(targetUserId)) return send(client,{type:'social_error',message:'That player is not in your friend list.'});
  const target=onlineClientForUser(targetUserId); const room=target?.room?rooms.get(target.room):null;
  if(!target || !room || !target.inMatch) return send(client,{type:'social_error',message:'That friend is no longer in a match.'});
  const settings=target.profile?.profile_settings||{};
  if(!modeRules(room.mode).spectate || !privacyAllows(settings.allow_spectate||'friends',true,samePartyUsers(client,target))) return send(client,{type:'social_error',message:'Spectating is disabled for this match.'});
  removeFromRoom(client);
  client.room=room.code; client.role='spectator'; client.inMatch=false; room.spectators.add(client); room.emptySince=0;
  const canJoin=roomJoinWindowOpen(room) && room.clients.size<roomCapacity(room) && privacyAllows(settings.allow_join||'friends',true,samePartyUsers(client,target));
  send(client,{type:'spectator_start',mode:room.mode,matchId:room.matchId,targetUserId,targetClientId:target.id,targetName:target.name,joinable:!!canJoin});
  const peers=peersFor(client); if(peers.length) send(client,{type:'peers',peers});
  send(client,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)}); sendSharedState(client,room,true);
  broadcastPresenceForUser(client.userId);
}
function joinFriend(client,targetUserId){
  targetUserId=cleanUserId(targetUserId);
  if(!client.friendIds?.has(targetUserId)) return send(client,{type:'join_denied',message:'That player is not in your friend list.'});
  const target=onlineClientForUser(targetUserId); const room=target?.room?rooms.get(target.room):null;
  if(!target || !room || !target.inMatch) return send(client,{type:'join_denied',message:'That friend is no longer in a match.'});
  const rules=modeRules(room.mode),settings=target.profile?.profile_settings||{};
  if(!roomJoinWindowOpen(room)) return send(client,{type:'join_denied',message:room.mode==='bossrush'?'Boss Rush can only be joined between boss phases.':'Joining is closed for Battle Royale and locked matches.'});
  if(room.clients.size>=rules.capacity) return send(client,{type:'join_denied',message:'That match is full.'});
  if(!privacyAllows(settings.allow_join||'friends',true,samePartyUsers(client,target))) return send(client,{type:'join_denied',message:'That friend does not allow joining.'});
  joinClientToRoom(client,room,{mode:room.mode,name:client.name,spawnNearClient:target,matchTeam:room.mode==='teams'?target.serverTeam:null});
  send(client,{type:'social_notice',message:'Joined '+target.name+'\'s match.'});
}

async function friendRequestProfilesByIds(ids){
  const clean=[...new Set((ids||[]).map(cleanUserId).filter(Boolean))];
  if(!clean.length)return new Map();
  const rows=await supabaseAdminRequest(
    '/rest/v1/profiles'
    +'?id=in.('+clean.join(',')+')'
    +'&select=id,username,friend_code,profile_icon,equipped_title',
    {method:'GET'}
  );
  return new Map((Array.isArray(rows)?rows:[]).map(profile=>[profile.id,profile]));
}
async function friendRequestStateForUser(userId){
  userId=cleanUserId(userId);
  if(!userId)return{incoming:[],outgoing:[]};
  const rows=await supabaseAdminRequest(
    '/rest/v1/friend_requests'
    +'?or=(sender_user_id.eq.'+encodeURIComponent(userId)+',receiver_user_id.eq.'+encodeURIComponent(userId)+')'
    +'&status=eq.pending'
    +'&select=id,sender_user_id,receiver_user_id,status,created_at,updated_at'
    +'&order=created_at.desc',
    {method:'GET'}
  );
  const requests=Array.isArray(rows)?rows:[];
  const profileIds=requests.flatMap(row=>[row.sender_user_id,row.receiver_user_id]);
  const profiles=await friendRequestProfilesByIds(profileIds);
  const view=row=>{
    const otherId=row.sender_user_id===userId?row.receiver_user_id:row.sender_user_id;
    const profile=profiles.get(otherId)||{};
    return{
      id:Number(row.id),
      userId:otherId,
      username:profile.username||'Player',
      friendCode:profile.friend_code||'',
      profileIcon:profile.profile_icon||'core:circle',
      title:profile.equipped_title||'',
      createdAt:row.created_at
    };
  };
  return{
    incoming:requests.filter(row=>row.receiver_user_id===userId).map(view),
    outgoing:requests.filter(row=>row.sender_user_id===userId).map(view)
  };
}
async function sendFriendRequestState(client){
  if(!client?.authenticated||client.isGuest||!client.userId)return;
  const state=await friendRequestStateForUser(client.userId);
  send(client,{type:'friend_request_state',...state});
}
async function refreshFriendUsers(userIds){
  const clean=[...new Set((userIds||[]).map(cleanUserId).filter(Boolean))];
  for(const userId of clean){
    for(const session of allOnlineClientsForUser(userId)){
      try{await refreshClientFriends(session);}catch(error){}
      try{await sendFriendRequestState(session);}catch(error){}
      sendWatchedPresence(session);
    }
    broadcastPresenceForUser(userId);
  }
}
async function sendFriendRequestByCode(client,msg){
  if(!client.authenticated||!client.userId)throw new Error('Login before sending friend requests.');
  const now=Date.now();
  if(now-(client.lastFriendRequestAt||0)<3000)throw new Error('Wait before sending another friend request.');
  const code=String(msg.friendCode||'').trim().toUpperCase().replace(/[^A-Z0-9-]/g,'').slice(0,16);
  if(!code)throw new Error('Enter a valid friend code.');

  const profiles=await supabaseAdminRequest(
    '/rest/v1/profiles'
    +'?friend_code=eq.'+encodeURIComponent(code)
    +'&select=id,username,friend_code&limit=1',
    {method:'GET'}
  );
  const target=Array.isArray(profiles)?profiles[0]:null;
  if(!target)throw new Error('No account uses that friend code.');
  if(target.id===client.userId)throw new Error('You cannot send a request to yourself.');

  await refreshClientFriends(client);
  if(client.friendIds.has(target.id))throw new Error(target.username+' is already your friend.');

  const reverse=await supabaseAdminRequest(
    '/rest/v1/friend_requests'
    +'?sender_user_id=eq.'+encodeURIComponent(target.id)
    +'&receiver_user_id=eq.'+encodeURIComponent(client.userId)
    +'&status=eq.pending'
    +'&select=id&limit=1',
    {method:'GET'}
  );
  if(Array.isArray(reverse)&&reverse[0]){
    throw new Error(target.username+' already sent you a request. Accept it from Friends & Party.');
  }

  client.lastFriendRequestAt=now;
  await supabaseAdminRequest(
    '/rest/v1/friend_requests?on_conflict=sender_user_id,receiver_user_id',
    {
      method:'POST',
      headers:{Prefer:'resolution=merge-duplicates,return=minimal'},
      body:JSON.stringify({
        sender_user_id:client.userId,
        receiver_user_id:target.id,
        status:'pending',
        created_at:new Date().toISOString(),
        updated_at:new Date().toISOString(),
        responded_at:null
      })
    }
  );

  await refreshFriendUsers([client.userId,target.id]);
  for(const session of allOnlineClientsForUser(target.id)){
    send(session,{
      type:'social_notice',
      message:(client.profile?.username||client.name||'A player')+' sent you a friend request.'
    });
  }
  send(client,{type:'friend_request_sent',targetUserId:target.id,targetName:target.username});
}
async function acceptFriendRequest(client,msg){
  if(!client.authenticated||!client.userId)throw new Error('Login before accepting friend requests.');
  const requestId=Math.floor(Number(msg.requestId));
  if(!Number.isSafeInteger(requestId)||requestId<1)throw new Error('Invalid friend request.');

  const rows=await supabaseAdminRequest(
    '/rest/v1/friend_requests'
    +'?id=eq.'+requestId
    +'&receiver_user_id=eq.'+encodeURIComponent(client.userId)
    +'&status=eq.pending'
    +'&select=id,sender_user_id,receiver_user_id&limit=1',
    {method:'GET'}
  );
  const request=Array.isArray(rows)?rows[0]:null;
  if(!request)throw new Error('That friend request is no longer available.');

  await supabaseAdminRequest(
    '/rest/v1/friend_requests?id=eq.'+requestId,
    {
      method:'PATCH',
      headers:{Prefer:'return=minimal'},
      body:JSON.stringify({
        status:'accepted',
        responded_at:new Date().toISOString(),
        updated_at:new Date().toISOString()
      })
    }
  );

  await supabaseAdminRequest(
    '/rest/v1/friendships?on_conflict=user_id,friend_id',
    {
      method:'POST',
      headers:{Prefer:'resolution=merge-duplicates,return=minimal'},
      body:JSON.stringify([
        {user_id:request.sender_user_id,friend_id:request.receiver_user_id},
        {user_id:request.receiver_user_id,friend_id:request.sender_user_id}
      ])
    }
  );

  await supabaseAdminRequest(
    '/rest/v1/friend_requests'
    +'?sender_user_id=eq.'+encodeURIComponent(request.receiver_user_id)
    +'&receiver_user_id=eq.'+encodeURIComponent(request.sender_user_id)
    +'&status=eq.pending',
    {
      method:'PATCH',
      headers:{Prefer:'return=minimal'},
      body:JSON.stringify({
        status:'accepted',
        responded_at:new Date().toISOString(),
        updated_at:new Date().toISOString()
      })
    }
  ).catch(()=>{});

  await refreshFriendUsers([request.sender_user_id,request.receiver_user_id]);
  for(const userId of [request.sender_user_id,request.receiver_user_id]){
    for(const session of allOnlineClientsForUser(userId)){
      send(session,{type:'friend_request_accepted',friendUserId:userId===request.sender_user_id?request.receiver_user_id:request.sender_user_id});
    }
  }
}
async function closeFriendRequest(client,msg,status){
  if(!client.authenticated||!client.userId)throw new Error('Login before managing friend requests.');
  const requestId=Math.floor(Number(msg.requestId));
  if(!Number.isSafeInteger(requestId)||requestId<1)throw new Error('Invalid friend request.');
  const filter=status==='cancelled'
    ?'&sender_user_id=eq.'+encodeURIComponent(client.userId)
    :'&receiver_user_id=eq.'+encodeURIComponent(client.userId);
  const rows=await supabaseAdminRequest(
    '/rest/v1/friend_requests?id=eq.'+requestId+filter+'&status=eq.pending&select=id,sender_user_id,receiver_user_id&limit=1',
    {method:'GET'}
  );
  const request=Array.isArray(rows)?rows[0]:null;
  if(!request)throw new Error('That friend request is no longer available.');
  await supabaseAdminRequest('/rest/v1/friend_requests?id=eq.'+requestId,{
    method:'PATCH',
    headers:{Prefer:'return=minimal'},
    body:JSON.stringify({
      status,
      responded_at:new Date().toISOString(),
      updated_at:new Date().toISOString()
    })
  });
  await refreshFriendUsers([request.sender_user_id,request.receiver_user_id]);
}
async function removeMutualFriend(client,msg){
  if(!client.authenticated||!client.userId)throw new Error('Login before removing friends.');
  const targetUserId=cleanUserId(msg.targetUserId);
  if(!targetUserId||targetUserId===client.userId)throw new Error('Invalid friend.');
  await supabaseAdminRequest(
    '/rest/v1/friendships'
    +'?or=(and(user_id.eq.'+encodeURIComponent(client.userId)+',friend_id.eq.'+encodeURIComponent(targetUserId)+'),and(user_id.eq.'+encodeURIComponent(targetUserId)+',friend_id.eq.'+encodeURIComponent(client.userId)+'))',
    {method:'DELETE',headers:{Prefer:'return=minimal'}}
  );
  await refreshFriendUsers([client.userId,targetUserId]);
  send(client,{type:'friendship_removed',friendUserId:targetUserId});
}

function handleMessage(client, msg){
  if(typeof msg !== 'object' || !msg) return;
  client.lastSeen=Date.now();

  if(msg.type === 'guest_authenticate'){
    try{authenticateGuestSocket(client,msg);}catch(error){send(client,{type:'auth_error',message:error.message||'Guest connection failed.'});}
    return;
  }
  if(msg.type === 'authenticate'){
    authenticateSocket(client,msg.accessToken).catch(error=>send(client,{type:'auth_error',message:error.message||'Authentication failed.'}));
    return;
  }
  if(msg.type === 'social_refresh'){
    Promise.all([refreshClientProfile(client),refreshClientFriends(client)])
      .then(async()=>{
        sendWatchedPresence(client);
        sendPartyStateForClient(client);
        try{await sendFriendRequestState(client);}catch(error){}
        broadcastPresenceForUser(client.userId);
      })
      .catch(error=>send(client,{type:'social_error',message:error.message||'Could not refresh social data.'}));
    return;
  }
  if(msg.type === 'presence_request'){ sendWatchedPresence(client); return; }

  if(msg.type === 'friend_request_refresh'){
    sendFriendRequestState(client).catch(error=>send(client,{type:'social_error',message:error.message||'Could not load friend requests.'}));
    return;
  }
  if(msg.type === 'friend_request_send'){
    sendFriendRequestByCode(client,msg).catch(error=>send(client,{type:'social_error',message:error.message||'Could not send friend request.'}));
    return;
  }
  if(msg.type === 'friend_request_accept'){
    acceptFriendRequest(client,msg).catch(error=>send(client,{type:'social_error',message:error.message||'Could not accept friend request.'}));
    return;
  }
  if(msg.type === 'friend_request_decline'){
    closeFriendRequest(client,msg,'declined').catch(error=>send(client,{type:'social_error',message:error.message||'Could not decline friend request.'}));
    return;
  }
  if(msg.type === 'friend_request_cancel'){
    closeFriendRequest(client,msg,'cancelled').catch(error=>send(client,{type:'social_error',message:error.message||'Could not cancel friend request.'}));
    return;
  }
  if(msg.type === 'friend_remove_mutual'){
    removeMutualFriend(client,msg).catch(error=>send(client,{type:'social_error',message:error.message||'Could not remove friend.'}));
    return;
  }

  if(msg.type === 'party_invite'){ handlePartyInvite(client,msg.targetUserId); return; }
  if(msg.type === 'party_accept'){ acceptPartyInvite(client,msg.inviteId); return; }
  if(msg.type === 'party_decline'){ pendingPartyInvites.delete(String(msg.inviteId||'')); return; }
  if(msg.type === 'party_leave'){
    const p=partyForClient(client); if(p) leavePartyUser(client.userId,p); return;
  }
  if(msg.type === 'party_ready'){
    const p=partyForClient(client); if(p){p.ready.set(client.userId,!!msg.ready);broadcastParty(p);} return;
  }
  if(msg.type === 'party_mode'){
    const p=partyForClient(client); if(p&&p.leaderId===client.userId&&!p.queued){p.mode=cleanMode(msg.mode);p.fillBots=msg.fillBots!==false;for(const uid of p.members)p.ready.set(uid,uid===p.leaderId);broadcastParty(p);} return;
  }
  if(msg.type === 'queue_join'){ if(!client.authenticated)return send(client,{type:'queue_error',message:'Connect before matchmaking.'}); queueEntry(client,msg.mode,msg.asParty!==false,msg.fillBots!==false); return; }
  if(msg.type === 'queue_cancel'){ cancelClientQueue(client); return; }
  if(msg.type === 'spectate_friend'){ spectateFriend(client,msg.friendUserId); return; }
  if(msg.type === 'join_friend'){ joinFriend(client,msg.friendUserId); return; }

  if(msg.type === 'report_player'){
    submitPersistentPlayerReport(client,msg)
      .then(()=>send(client,{type:'social_notice',message:'Report submitted for moderator review.'}))
      .catch(error=>send(client,{type:'social_error',message:error.message||'Could not submit report.'}));
    return;
  }
  if(msg.type === 'party_ping'){
    if(!client.authenticated || !client.room || !client.inMatch) return;
    const now=Date.now();
    const pingWait=2500-(now-(client.lastPartyPingAt||0));
    if(pingWait>0){
      send(client,{type:'social_notice',message:`Quick Ping cooldown: wait ${(pingWait/1000).toFixed(1)}s.`});
      return;
    }
    const party=partyForClient(client); if(!party || party.members.size<2) return;
    const kind=safeToken(msg.kind,24); if(!['enemy','fragment','boss','retreat','group','solarbum'].includes(kind)) return;
    const room=rooms.get(client.room); if(!room) return;
    client.lastPartyPingAt=now;
    const payload={type:'party_ping',kind,x:finiteNumber(msg.x,client.snapshot?.x||0,-HALF_W,HALF_W),y:finiteNumber(msg.y,client.snapshot?.y||0,-HALF_H,HALF_H),sourceName:client.name,userId:client.userId};
    for(const uid of party.members) for(const member of allOnlineClientsForUser(uid)) if(member.room===room.code) send(member,payload);
    return;
  }
  if(msg.type === 'leave_match'){
    const party=partyForClient(client);
    removeFromRoom(client);
    send(client,{type:'left_match'});
    sendPartyStateForClient(client);
    if(party)broadcastParty(party);
    sendWatchedPresence(client);
    return;
  }

  if(msg.type === 'public_role_request'){
    const targetUserId=cleanUserId(msg.userId);
    if(!client.authenticated||!targetUserId) return;
    loadAccountRole(targetUserId)
      .then(accountRole=>send(client,{type:'public_account_role',userId:targetUserId,accountRole:publicAccountRole(accountRole)}))
      .catch(()=>send(client,{type:'public_account_role',userId:targetUserId,accountRole:'player'}));
    return;
  }
  if(msg.type === 'developer_request_panel'){
    if(!requireDeveloper(client)) return;
    developerPanelData()
      .then(data=>send(client,{type:'developer_panel_data',...data}))
      .catch(error=>moderatorError(client,error,'Could not load Developer Panel data.'));
    return;
  }
  if(msg.type === 'developer_announcement'){
    developerCreateAnnouncement(client,msg).catch(error=>moderatorError(client,error,'Could not send announcement.'));
    return;
  }
  if(msg.type === 'developer_warn'){
    developerWarnPlayer(client,msg).catch(error=>moderatorError(client,error,'Could not warn that player.'));
    return;
  }
  if(msg.type === 'developer_kick'){
    developerKickPlayer(client,msg).catch(error=>moderatorError(client,error,'Could not kick that player.'));
    return;
  }
  if(msg.type === 'developer_mute'){
    createSanction(client,msg,'mute').catch(error=>moderatorError(client,error,'Could not mute that player.'));
    return;
  }
  if(msg.type === 'developer_ban'){
    createSanction(client,msg,'ban').catch(error=>moderatorError(client,error,'Could not suspend that account.'));
    return;
  }
  if(msg.type === 'developer_lift_sanction'){
    developerLiftSanction(client,msg).catch(error=>moderatorError(client,error,'Could not lift that sanction.'));
    return;
  }
  if(msg.type === 'developer_update_report'){
    developerUpdateReport(client,msg).catch(error=>moderatorError(client,error,'Could not update that report.'));
    return;
  }


  if(msg.type === 'developer_debug_open'){
    openDeveloperDebugSession(client).catch(error=>{
      if(isDeveloper(client)) send(client,{type:'developer_debug_unavailable',message:'The secure debug session could not be opened.'});
    });
    return;
  }
  if(msg.type === 'developer_debug_close'){
    if(isDeveloper(client)) revokeDeveloperDebug(client,false);
    return;
  }
  if(msg.type === 'developer_debug_action'){
    executeDeveloperDebugAction(client,msg).catch(error=>{
      if(isDeveloper(client)) send(client,{type:'developer_debug_action_rejected',requestId:safeToken(msg.requestId,64)});
    });
    return;
  }

  if(msg.type === 'join'){
    const room=getRoom(msg.room); if(room.clients.size===0){room.mode=cleanMode(msg.mode);room.fillBots=true;}
    joinClientToRoom(client,room,{mode:room.mode,name:msg.name});
    return;
  }

  if(!client.room) return;
  const room=rooms.get(client.room);
  if(!room) return;
  if(client.role==='spectator' && msg.type!=='chat') return;

  if(msg.type === 'mode_change'){
    if(client.id!==room.leaderId || room.matchStarted) return;
    room.mode=cleanMode(msg.mode);
    assignRoomTeams(room);
    for(const c of room.clients) c.ready=false;
    broadcastLobby(room);
  }else if(msg.type === 'ready'){
    if(room.matchStarted) return;
    client.ready=!!msg.ready;
    if(msg.mode && client.id===room.leaderId){
      room.mode=cleanMode(msg.mode);
      assignRoomTeams(room);
    }
    broadcastLobby(room);
    maybeStartMatch(room);
  }else if(msg.type === 'bossrush_join_window'){
    if(room.mode!=='bossrush' || client.id!==room.leaderId) return;
    room.bossRushJoinOpen=!!msg.open;
    room.bossRushPhase=safeToken(msg.phase||'phase',32)||'phase';
    for(const c of room.clients) broadcastPresenceForUser(c.userId);
  }else if(msg.type === 'state'){
    client.snapshot=sanitizeSnapshot(client,room,msg.snapshot);
    broadcast(room.code,{type:'peer_state',clientId:client.id,snapshot:client.snapshot},client);
  }else if(msg.type === 'projectile'){
    const options=sanitizeProjectileOptions(room,client,msg.options);
    broadcast(room.code,{
      type:'projectile',
      ownerId:client.id,
      originEntityId:safeToken(msg.originEntityId||'',64),
      angle:finiteNumber(msg.angle,client.snapshot?.angle||0,-Math.PI*8,Math.PI*8),
      options
    },client);
  }else if(msg.type === 'ability_event'){
    const abilityId=safeToken(msg.abilityId,48);
    if(!abilityId) return;
    broadcast(room.code,{
      type:'ability_event',
      ownerId:client.id,
      abilityId,
      slotIndex:Math.floor(finiteNumber(msg.slotIndex,1,1,4)),
      evolved:!!msg.evolved,
      angle:finiteNumber(msg.angle,client.snapshot?.angle||0,-Math.PI*8,Math.PI*8),
      x:finiteNumber(msg.x,client.snapshot?.x||0,-HALF_W,HALF_W),
      y:finiteNumber(msg.y,client.snapshot?.y||0,-HALF_H,HALF_H)
    },client);
  }else if(msg.type === 'hit'){
    const target=getClientById(room,String(msg.targetId||''));
    if(!target || target===client || !target.inMatch || !target.snapshot || target.snapshot.dead) return;
    if(sameCombatTeam(client.serverTeam,target.serverTeam)) return;
    const amount=clamp(finiteNumber(msg.amount,0),0,developerDebugSnapshotAuthorized(client)?1000:450);
    if(amount<=0) return;
    sendDamageToClient(target,{
      type:'hit',
      targetId:target.id,
      amount,
      sourceId:client.id,
      sourceUserId:client.userId||'',
      sourceName:client.name,
      attack:safeToken(msg.attack||client.snapshot?.archetype||'player_attack',48)
    });
  }else if(msg.type === 'fragment_collect'){
    collectSharedFragment(room,client,String(msg.id||''));
  }else if(msg.type === 'boss_hit'){
    const boss=room.bosses.find(b=>b.id===String(msg.bossId||''));
    if(!boss || boss.dead) return;
    const amount=clamp(finiteNumber(msg.amount,0),0,450);
    boss.hp-=amount;
    if(boss.hp<=0){
      boss.hp=0; boss.dead=true; boss.removeAt=Date.now()+650;
      const bossDrops=spawnDeathFragmentBurst(room,boss.x,boss.y,30,'boss_death',0);
      const abilityDrop=spawnSharedFragment(room,'ability',boss.x,boss.y,['judgement_laser','fragment_storm','reflect_shield','loot_radar'][irand(0,4)]);
      bossDrops.push(abilityDrop);
      broadcastFragmentBatch(room,[abilityDrop],'boss_ability_drop');
      send(client,{type:'boss_award',bossId:boss.id,bossName:boss.name,xp:520,score:2800});
      broadcast(room.code,{type:'boss_event',action:'killed',bossId:boss.id,bossName:boss.name,killerId:client.id,killerName:client.name});
    }
  }else if(msg.type === 'bot_hit'){
    const bot=room.bots.find(b=>b.id===String(msg.botId||''));
    if(!bot || bot.dead) return;
    if(sameCombatTeam(client.serverTeam,bot.team)) return;
    damageServerBot(room,bot,clamp(finiteNumber(msg.amount,0),0,250),{
      kind:'player',
      id:client.id,
      name:client.name,
      client
    });
  }else if(msg.type === 'player_death'){
    const now=Date.now();
    if(now-(client.lastDeathDropAt||0)<1800) return;
    client.lastDeathDropAt=now;

    const snap=msg.snapshot||client.snapshot||{};
    client.spawnProtectedUntil=0;
    if(client.snapshot) client.snapshot.dead=true;
    const x=clamp(finiteNumber(snap.x,0),-HALF_W+50,HALF_W-50);
    const y=clamp(finiteNumber(snap.y,0),-HALF_H+50,HALF_H-50);
    const carried=clamp(finiteNumber(snap.frags,0),0,100);
    const dropCount=clamp(Math.floor(16+carried*.72),16,46);

    spawnDeathFragmentBurst(room,x,y,dropCount,'player_death',.18);
    broadcast(room.code,{type:'death_event',clientId:client.id,name:client.name,snapshot:snap,killer:msg.killer||null},client);
  }else if(msg.type === 'chat'){
    const now=Date.now();
    const body=String(msg.msg||'').replace(/[<>]/g,'').trim().slice(0,120);
    if(!body) return;

    const chatWait=1500-(now-(client.lastChatAt||0));
    if(chatWait>0){
      send(client,{type:'chat',name:'SERVER',msg:`Chat cooldown: wait ${(chatWait/1000).toFixed(1)}s.`});
      return;
    }

    if(now<(client.moderationMutedUntil||0)){
      const seconds=Math.max(1,Math.ceil((client.moderationMutedUntil-now)/1000));
      send(client,{type:'chat',name:'SERVER',msg:`You are muted for another ${seconds}s.`});
      return;
    }

    if(now<(client.chatMutedUntil||0)){
      const seconds=Math.max(1,Math.ceil((client.chatMutedUntil-now)/1000));
      send(client,{type:'chat',name:'SERVER',msg:`Chat cooldown: wait ${seconds}s.`});
      return;
    }

    client.chatTimes=(client.chatTimes||[]).filter(t=>now-t<5000);
    const duplicate=body.toLowerCase()===(client.lastChatBody||'').toLowerCase() && now-(client.lastChatAt||0)<4000;
    if(duplicate){
      send(client,{type:'chat',name:'SERVER',msg:'Duplicate message blocked.'});
      return;
    }

    if(client.chatTimes.length>=4){
      client.chatMutedUntil=now+9000;
      client.chatTimes=[];
      send(client,{type:'chat',name:'SERVER',msg:'Chat spam detected. Muted for 9 seconds.'});
      return;
    }

    client.chatTimes.push(now);
    client.lastChatBody=body;
    client.lastChatAt=now;
    broadcast(room.code,{type:'chat',name:client.name,msg:body,accountRole:publicAccountRole(client.accountRole),userId:client.userId||''});
  }else if(msg.type === 'event'){
    const eventType=safeToken(msg.eventType||msg.name||'',48);
    broadcast(room.code,{...msg,eventType,sourceId:client.id},client);
  }
}
function decodeFrames(client, chunk){
  if(!Buffer.isBuffer(chunk) || !chunk.length) return;
  client.lastSeen=Date.now();
  client.buffer=client.buffer?Buffer.concat([client.buffer,chunk]):chunk;
  if(client.buffer.length>MAX_FRAME_BYTES*2){client.socket.destroy();return;}
  let offset=0;
  while(client.buffer.length-offset>=2){
    const b0=client.buffer[offset];
    const opcode=b0&0x0f;
    const b1=client.buffer[offset+1];
    const masked=(b1&0x80)!==0;
    let len=b1&0x7f;
    let header=2;
    if(len===126){
      if(client.buffer.length-offset<4) break;
      len=client.buffer.readUInt16BE(offset+2); header=4;
    }else if(len===127){
      if(client.buffer.length-offset<10) break;
      const big=client.buffer.readBigUInt64BE(offset+2);
      if(big>BigInt(MAX_FRAME_BYTES)){client.socket.destroy();return;}
      len=Number(big); header=10;
    }
    if(len>MAX_FRAME_BYTES){client.socket.destroy();return;}
    const maskBytes=masked?4:0;
    if(client.buffer.length-offset<header+maskBytes+len) break;
    let payload=client.buffer.subarray(offset+header+maskBytes,offset+header+maskBytes+len);
    if(masked){
      const mask=client.buffer.subarray(offset+header,offset+header+4);
      payload=Buffer.from(payload.map((byte,i)=>byte^mask[i%4]));
    }
    offset+=header+maskBytes+len;
    if(opcode===0x8){client.socket.end();return;}
    if(opcode===0x9){sendPong(client);continue;}
    if(opcode!==0x1) continue;
    try{
      const parsed=JSON.parse(payload.toString('utf8'));
      handleMessage(client,parsed);
    }catch(e){
      if(Date.now()-(client.lastParseErrorAt||0)>5000){
        client.lastParseErrorAt=Date.now();
        console.warn('[Fragment.io] Ignored malformed client packet:',e.message);
      }
    }
  }
  client.buffer=client.buffer.subarray(offset);
}
function sendPong(client){ try{ client.socket.write(Buffer.from([0x8a, 0])); }catch(e){} }
function serveFile(req, res){
  let pathname;
  try{ pathname=decodeURIComponent(url.parse(req.url).pathname||'/'); }
  catch(e){ res.writeHead(400,{'Content-Type':'text/plain; charset=utf-8'}); res.end('Bad Request'); return; }

  if(pathname==='/supabase-config.js'){
    const config={
      url:String(process.env.SUPABASE_URL||'').trim(),
      key:String(process.env.SUPABASE_PUBLISHABLE_KEY||'').trim()
    };
    res.writeHead(200,{
      'Content-Type':'text/javascript; charset=utf-8',
      'Cache-Control':'no-store, max-age=0',
      'X-Content-Type-Options':'nosniff'
    });
    res.end('window.FRAGMENT_SUPABASE_CONFIG='+JSON.stringify(config)+';');
    return;
  }

  if(pathname==='/account-config-status'){
    const supabaseUrl=String(process.env.SUPABASE_URL||'').trim();
    const publishableKey=String(process.env.SUPABASE_PUBLISHABLE_KEY||'').trim();
    const body={
      configured:!!supabaseUrl && !!publishableKey,
      urlConfigured:!!supabaseUrl,
      keyConfigured:!!publishableKey,
      urlLooksValid:/^https:\/\/[a-z0-9-]+\.supabase\.co$/i.test(supabaseUrl),
      keyLooksValid:publishableKey.startsWith('sb_publishable_') || publishableKey.startsWith('eyJ')
    };
    res.writeHead(body.configured?200:503,{
      'Content-Type':'application/json; charset=utf-8',
      'Cache-Control':'no-store'
    });
    res.end(JSON.stringify(body));
    return;
  }

  if(pathname==='/') pathname='/index.html';
  const filePath=path.resolve(ROOT,'.'+pathname);
  if(filePath!==ROOT && !filePath.startsWith(ROOT+path.sep)){
    res.writeHead(403,{'Content-Type':'text/plain; charset=utf-8'}); res.end('Forbidden'); return;
  }
  fs.readFile(filePath,(err,data)=>{
    if(err){res.writeHead(404,{'Content-Type':'text/plain; charset=utf-8'});res.end('Not found');return;}
    const types={
      '.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8','.css':'text/css; charset=utf-8',
      '.json':'application/json; charset=utf-8','.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg',
      '.gif':'image/gif','.svg':'image/svg+xml','.ico':'image/x-icon','.webp':'image/webp',
      '.mp3':'audio/mpeg','.wav':'audio/wav','.ogg':'audio/ogg'
    };
    res.writeHead(200,{'Content-Type':types[path.extname(filePath).toLowerCase()]||'application/octet-stream','Cache-Control':'no-store'});
    res.end(data);
  });
}
const server = http.createServer(serveFile);
server.on('upgrade', (req, socket) => {
  if(url.parse(req.url).pathname !== '/ws'){ socket.destroy(); return; }
  const key = req.headers['sec-websocket-key'];
  if(!key){ socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write([
    'HTTP/1.1 101 Switching Protocols',
    'Upgrade: websocket',
    'Connection: Upgrade',
    `Sec-WebSocket-Accept: ${accept}`,
    '', ''
  ].join('\r\n'));
  const client = {
    id:id(), socket, room:null, name:'Player', snapshot:null, buffer:null,
    ready:false, inMatch:false, role:'social', serverTeam:'neutral', spawnProtectedUntil:0,
    authenticated:false, isGuest:false, accessToken:'', userId:null, accountRole:'player', profile:null, progress:null, friendIds:new Set(), partyId:null, queueId:null, matchTeam:null,
    lastSeen:Date.now(), lastParseErrorAt:0,
    chatTimes:[], chatMutedUntil:0, moderationMutedUntil:0, lastChatBody:'', lastChatAt:0,
    lastPartyPingAt:0, lastReportAt:0, lastAnnouncementAt:0, lastFriendRequestAt:0,
    developerDebugSession:null, developerDebugRootAdminUntil:0,
    lastDeathDropAt:0
  };
  clients.add(client);
  socket.on('data', chunk => decodeFrames(client, chunk));
  const cleanup=()=>{
    if(client.cleanedUp)return;
    client.cleanedUp=true;
    const party=partyForClient(client);
    if(client.userId&&client.room&&client.inMatch){
      reconnectReservations.set(client.userId,{roomCode:client.room,expires:Date.now()+60000});
    }
    removeFromRoom(client);
    cancelClientQueue(client);
    clients.delete(client);
    if(client.userId){
      const set=userClients.get(client.userId);
      if(set){
        set.delete(client);
        if(!set.size)userClients.delete(client.userId);
      }
      broadcastPresenceForUser(client.userId);
    }
    if(party)broadcastParty(party);
  };
  socket.on('close', cleanup);
  socket.on('error', cleanup);
});
function tickRoomSafely(code, room, dt){
  try{
    updateServerBots(room,dt);
    updateSharedWorld(room,dt);
    updateSharedBosses(room,dt);
    updateSharedBroadcasts(room);
  }catch(err){
    const now=Date.now();
    if(now-(room.lastErrorAt||0)>4000){
      room.lastErrorAt=now;
      console.error(`[Fragment.io] Recovered room ${code} tick error:`,err);
    }
  }
}
setInterval(()=>{
  for(const [code,room] of rooms){
    if(room.clients.size===0 && (!room.spectators||room.spectators.size===0)){
      if(!room.matchStarted || (room.emptySince && Date.now()-room.emptySince>60000)){rooms.delete(code);continue;}
    }
    tickRoomSafely(code,room,50);
  }
},50);
setInterval(processMatchQueues,1000);
setInterval(()=>{
  for(const client of clients){
    if(client.authenticated)sendWatchedPresence(client);
  }
  for(const party of parties.values()){
    if(party.members.size)broadcastParty(party);
  }
},1800);
setInterval(()=>{
  const now=Date.now();
  for(const [code,room] of rooms){
    if(room.clients.size===0 && (!room.spectators||room.spectators.size===0)){
      if(!room.matchStarted || (room.emptySince && now-room.emptySince>60000)){rooms.delete(code);continue;}
    }
    for(const client of [...room.clients]){
      if(client.socket.destroyed || now-(client.lastSeen||now)>90000){
        try{client.socket.destroy();}catch(e){}
        removeFromRoom(client);
        clients.delete(client);
      }
    }
    if(room.clients.size) broadcastLobby(room);
  }
},5000);
server.listen(PORT, "0.0.0.0", () => {
  console.log(`Fragment.io social/matchmaking server running on port ${PORT}`);
  console.log('Friend presence, parties, spectating, joining, hidden matches, dynamic bot fill, and legacy rooms are enabled.');
});

// -----------------------------------------------------------------------------
// Fragment.io irregular island map synchronization patch
// -----------------------------------------------------------------------------
var sharedBiomes = [
  {id:'glacial',name:'Glacial Relay',effect:'Reduced acceleration',cx:0,cy:-2100,sx:2500,sy:1200,bias:-.05,x:-3150,y:-3150,w:6300,h:2550},
  {id:'verdant',name:'Verdant Divide',effect:'Gentle regeneration',cx:-2600,cy:-850,sx:2100,sy:1800,bias:0,x:-4600,y:-2600,w:3900,h:3600},
  {id:'furnace',name:'The Furnace',effect:'Fragments grant bonus XP',cx:-3000,cy:1200,sx:1900,sy:1700,bias:0,x:-4650,y:-250,w:3550,h:3000},
  {id:'sharddunes',name:'Shard Dunes',effect:'Fragment score increased',cx:-450,cy:2050,sx:2500,sy:1350,bias:.03,x:-2850,y:900,w:5100,h:2200},
  {id:'stormbreak',name:'Stormbreak Coast',effect:'Dash recharge increased',cx:3200,cy:-1250,sx:1500,sy:1150,bias:-.04,x:1950,y:-2600,w:2350,h:2350},
  {id:'skyglass',name:'Skyglass Expanse',effect:'Movement speed increased',cx:2900,cy:350,sx:1700,sy:1700,bias:0,x:1450,y:-900,w:2900,h:2950},
  {id:'terminus',name:'Elevator Terminus',effect:'Boss activity increased',cx:2450,cy:2100,sx:1450,sy:1150,bias:-.02,x:1200,y:1050,w:3000,h:2050},
  {id:'hub',name:'Shattered Hub',effect:'High-conflict neutral ground',cx:-150,cy:-250,sx:1050,sy:780,bias:-.16,x:-1500,y:-1250,w:2800,h:2050},
  {id:'nullgarden',name:'Null Garden',effect:'Natural fragments heal more',cx:850,cy:450,sx:850,sy:720,bias:-.18,x:-50,y:-300,w:1850,h:1650}
];

function islandServerGauss(nx,ny,cx,cy,sx,sy){
  const dx=(nx-cx)/sx,dy=(ny-cy)/sy;
  return Math.exp(-(dx*dx+dy*dy));
}
function islandServerField(x,y){
  const nx=x/HALF_W,ny=y/HALF_H;
  let value=1-Math.pow(Math.abs(nx)/.87,2.55)-Math.pow(Math.abs(ny)/.86,2.45);
  value+=.34*islandServerGauss(nx,ny,-.72,-.28,.34,.38);
  value+=.20*islandServerGauss(nx,ny,-.48,.68,.38,.30);
  value+=.26*islandServerGauss(nx,ny,.62,.60,.31,.33);
  value+=.18*islandServerGauss(nx,ny,.73,-.55,.28,.25);
  value+=.11*Math.sin(nx*8.4+ny*3.1)*Math.sin(ny*6.2-nx*2.2);
  value-=.54*islandServerGauss(nx,ny,.84,-.05,.22,.26);
  value-=.34*islandServerGauss(nx,ny,-.88,.20,.18,.30);
  value-=.45*islandServerGauss(nx,ny,-.02,.94,.26,.16);
  value-=.24*islandServerGauss(nx,ny,.10,-.92,.22,.14);
  return value;
}
function islandServerInside(x,y,margin=0){
  if(!Number.isFinite(x)||!Number.isFinite(y)||Math.abs(x)>HALF_W-5||Math.abs(y)>HALF_H-5)return false;
  return islandServerField(x,y)>(Math.max(0,Number(margin)||0)/Math.min(HALF_W,HALF_H)*1.12);
}
function islandServerNearest(x,y,margin=0){
  x=clamp(Number(x)||0,-HALF_W+10,HALF_W-10);
  y=clamp(Number(y)||0,-HALF_H+10,HALF_H-10);
  if(islandServerInside(x,y,margin))return{x,y};
  let lo=0,hi=1;
  for(let i=0;i<34;i++){
    const mid=(lo+hi)/2;
    if(islandServerInside(x*mid,y*mid,margin))lo=mid;else hi=mid;
  }
  let px=x*lo,py=y*lo;
  const len=Math.hypot(px,py)||1,inward=Math.max(10,margin*.18);
  px-=px/len*inward;py-=py/len*inward;
  if(!islandServerInside(px,py,margin)){px=0;py=0;}
  return{x:px,y:py};
}
function islandServerBiomeAt(x,y){
  if(!islandServerInside(x,y,0)){const p=islandServerNearest(x,y,0);x=p.x;y=p.y;}
  let best=sharedBiomes[0],bestScore=Infinity;
  for(let i=0;i<sharedBiomes.length;i++){
    const b=sharedBiomes[i],dx=(x-b.cx)/b.sx,dy=(y-b.cy)/b.sy;
    const score=dx*dx+dy*dy+(b.bias||0)+.09*Math.sin(x/690+i*1.7)*Math.cos(y/610-i*.9);
    if(score<bestScore){bestScore=score;best=b;}
  }
  return best;
}
function islandServerRandomPoint(margin=160,biomeId=null,minRadius=0){
  const desired=biomeId?sharedBiomes.find(b=>b.id===biomeId):null;
  for(let tries=0;tries<180;tries++){
    let x,y;
    if(desired){x=rand(desired.x+20,desired.x+desired.w-20);y=rand(desired.y+20,desired.y+desired.h-20);}
    else{x=rand(-HALF_W+80,HALF_W-80);y=rand(-HALF_H+80,HALF_H-80);}
    if(Math.hypot(x,y)<minRadius||!islandServerInside(x,y,margin))continue;
    if(desired&&islandServerBiomeAt(x,y).id!==desired.id)continue;
    return{x,y};
  }
  return desired?islandServerNearest(desired.cx,desired.cy,margin):{x:0,y:0};
}
function islandServerConstrainObject(obj,margin=40){
  if(!obj)return false;
  if(islandServerInside(obj.x,obj.y,margin))return false;
  const p=islandServerNearest(obj.x,obj.y,margin);
  obj.x=p.x;obj.y=p.y;obj.vx=(obj.vx||0)*.24;obj.vy=(obj.vy||0)*.24;
  return true;
}

randomArenaPoint=function(minRadius=0,margin=360){
  return islandServerRandomPoint(Math.max(80,margin),null,minRadius);
};

const islandOriginalSanitizeSnapshot=sanitizeSnapshot;
sanitizeSnapshot=function(client,room,raw){
  const snap=islandOriginalSanitizeSnapshot(client,room,raw);
  const p=islandServerNearest(snap.x,snap.y,(snap.r||18)+12);
  if(p.x!==snap.x||p.y!==snap.y){snap.x=p.x;snap.y=p.y;snap.vx*=.25;snap.vy*=.25;}
  for(const clone of snap.clones||[]){
    const cp=islandServerNearest(clone.x,clone.y,(clone.r||12)+8);clone.x=cp.x;clone.y=cp.y;
  }
  return snap;
};

const islandOriginalSpawnSharedFragment=spawnSharedFragment;
spawnSharedFragment=function(room,kind='xp',x=null,y=null,extra=null){
  const p=(x==null||y==null)?islandServerRandomPoint(30):islandServerNearest(x,y,30);
  return islandOriginalSpawnSharedFragment(room,kind,p.x,p.y,extra);
};

function spawnSharedTerrainFeature(room){
  const type=['crater','vine','ice','void','road'][irand(0,5)];
  const p=islandServerRandomPoint(type==='road'?150:180);
  const feature={
    id:'terrain_'+(++room.lastTerrainSerial)+'_'+id(3),
    type,x:p.x,y:p.y,life:rand(38,72),spawn:1.35,
    r:type==='road'?170:type==='vine'?120:type==='crater'?95:type==='void'?115:135,
    angle:rand(0,Math.PI)
  };
  room.terrainFeatures.push(feature);
  if(room.terrainFeatures.length>40)room.terrainFeatures.splice(0,room.terrainFeatures.length-40);
  broadcast(room.code,{type:'terrain_event',action:'spawn',terrain:terrainSnapshot(feature)});
  return feature;
}

setSharedHotZone=function(room){
  const b=sharedBiomes[irand(0,sharedBiomes.length)];
  room.hotZone={biome:b,timer:75,pulse:0,id:'hot_'+id(4)};
  room.nextHotZoneAt=Date.now()+rand(85000,110000);
  broadcast(room.code,{type:'hotzone_event',action:'set',hotZone:hotZoneSnapshot(room.hotZone)});
};

updateSharedMapSystems=function(room,dt){
  if(!room.matchStarted||room.mode==='bossrush')return;
  const now=Date.now();
  if(!room.hotZone&&now>(room.nextHotZoneAt||0)&&!['test','br'].includes(room.mode))setSharedHotZone(room);
  if(room.hotZone){
    room.hotZone.timer=Math.max(0,room.hotZone.timer-dt/1000);
    room.hotZone.pulse=(room.hotZone.pulse||0)+dt/1000;
    if(room.hotZone.timer<=0){
      room.hotZone=null;room.nextHotZoneAt=now+rand(85000,112000);
      broadcast(room.code,{type:'hotzone_event',action:'clear'});
    }else if(Math.random()<.035){
      const p=islandServerRandomPoint(45,room.hotZone.biome.id);
      spawnSharedFragment(room,Math.random()<.78?'xp':Math.random()<.65?'natural':'ability',p.x,p.y);
    }
  }
  if(now>(room.nextTerrainAt||0)&&!['test','br'].includes(room.mode)){
    room.nextTerrainAt=now+rand(9000,13500);
    if(Math.random()<.78)spawnSharedTerrainFeature(room);
  }
  for(let i=room.terrainFeatures.length-1;i>=0;i--){
    const f=room.terrainFeatures[i];f.life-=dt/1000;f.spawn=Math.max(0,(f.spawn||0)-dt/1000);
    islandServerConstrainObject(f,Math.min(180,(f.r||100)*.35));
    if(f.life<=0)room.terrainFeatures.splice(i,1);
  }
};

const islandOriginalActivateSharedWorld=activateSharedWorld;
activateSharedWorld=function(room,modeObj=null){
  const result=islandOriginalActivateSharedWorld(room,modeObj);
  for(const z of room.world.zones){
    const p=islandServerRandomPoint(Math.min(180,(z.r||250)*.28));z.x=p.x;z.y=p.y;
  }
  broadcast(room.code,{type:'world_event',action:'activate',world:room.world.mode,timer:room.world.timer,zones:room.world.zones});
  return result;
};

const islandOriginalSpawnSharedBoss=spawnSharedBoss;
spawnSharedBoss=function(room,forcedId=null){
  const b=islandOriginalSpawnSharedBoss(room,forcedId);
  if(b){
    const p=islandServerRandomPoint((b.r||48)+90,null,600);b.x=p.x;b.y=p.y;
    broadcast(room.code,{type:'bosses_state',bosses:room.bosses.map(bossSnapshot),immediate:true});
  }
  return b;
};

const islandOriginalUpdateServerBots=updateServerBots;
updateServerBots=function(room,dt){
  const result=islandOriginalUpdateServerBots(room,dt);
  let corrected=false;
  for(const bot of room.bots){
    if(islandServerConstrainObject(bot,(bot.r||18)+12)){
      const roam=islandServerRandomPoint(170);bot.roamX=roam.x;bot.roamY=roam.y;corrected=true;
    }
  }
  if(corrected&&Date.now()-(room.lastIslandCorrectionBroadcast||0)>180){
    room.lastIslandCorrectionBroadcast=Date.now();
    broadcast(room.code,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)});
  }
  return result;
};

const islandOriginalUpdateSharedBosses=updateSharedBosses;
updateSharedBosses=function(room,dt){
  const result=islandOriginalUpdateSharedBosses(room,dt);
  for(const boss of room.bosses)islandServerConstrainObject(boss,(boss.r||48)+70);
  return result;
};

const islandOriginalUpdateSharedWorld=updateSharedWorld;
updateSharedWorld=function(room,dt){
  const result=islandOriginalUpdateSharedWorld(room,dt);
  for(const f of room.fragments)islandServerConstrainObject(f,(f.r||9)+5);
  for(const z of room.world.zones)islandServerConstrainObject(z,Math.min(180,(z.r||250)*.28));
  for(const feature of room.terrainFeatures)islandServerConstrainObject(feature,Math.min(180,(feature.r||100)*.35));
  return result;
};

console.log('[Fragment.io] Irregular island map synchronization enabled.');

// -----------------------------------------------------------------------------
// v1.0 online boss abilities, fragment-storm authority, and 15-player normal
// -----------------------------------------------------------------------------
function v1BossActionSnapshot(room,b,action,data={}){
  broadcast(room.code,{type:'boss_action',bossId:b.id,boss:bossSnapshot(b),action,phase:data.phase||'warn',warn:finiteNumber(data.warn,0,0,5),x:finiteNumber(data.x,b.x,-HALF_W,HALF_W),y:finiteNumber(data.y,b.y,-HALF_H,HALF_H),fromX:finiteNumber(data.fromX,b.x,-HALF_W,HALF_W),fromY:finiteNumber(data.fromY,b.y,-HALF_H,HALF_H),angle:finiteNumber(data.angle,b.angle,-Math.PI*8,Math.PI*8),radius:finiteNumber(data.radius,220,0,1600),width:finiteNumber(data.width,54,0,300),range:finiteNumber(data.range,800,0,2000),duration:finiteNumber(data.duration,.6,.05,5),color:String(data.color||b.color||'#ffcf58').slice(0,24),label:String(data.label||'BOSS ATTACK').slice(0,36)});
}
function v1BossHitCircle(room,b,x,y,r,amount,cause){
  for(const snap of livePlayerSnapshots(room)){if(clientIsInvincible(snap.client))continue;if(Math.hypot(snap.x-x,snap.y-y)<=r+(snap.r||18))sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount,cause});}
}
function v1BossHitBeam(room,b,angle,range,width,amount,cause){
  const ca=Math.cos(angle),sa=Math.sin(angle);
  for(const snap of livePlayerSnapshots(room)){
    if(clientIsInvincible(snap.client))continue;
    const dx=snap.x-b.x,dy=snap.y-b.y,forward=dx*ca+dy*sa,side=Math.abs(-dx*sa+dy*ca);
    if(forward>0&&forward<range&&side<width+(snap.r||18))sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount,cause});
  }
}
function v1QueueBossAttack(room,b,target){
  const tx=target.snap.x,ty=target.snap.y,angle=Math.atan2(ty-b.y,tx-b.x),phase=b.hp< b.maxHp*.42?2:1;
  const choose=Math.random();let attack;
  if(b.bossKind==='elevator_authority')attack=choose<.58?{kind:'laser_sweep',warn:1.05,angle,range:1050,width:68,label:'ADMINISTRATIVE BEAM'}:{kind:'admin_pulse',warn:.78,x:b.x,y:b.y,radius:285,label:'ACCESS DENIED'};
  else if(b.bossKind==='telomere_warden')attack=choose<.68?{kind:'bio_bloom',warn:1.0,x:tx,y:ty,radius:235,label:'TELOMERE BLOOM'}:{kind:'heal',warn:.55,x:b.x,y:b.y,radius:190,label:'REPAIR CYCLE'};
  else if(b.bossKind==='exit_23')attack=choose<.62?{kind:'rocket_barrage',warn:.95,x:tx,y:ty,radius:250,label:'WRONG EXIT'}:{kind:'ghost_dash',warn:.72,x:tx,y:ty,fromX:b.x,fromY:b.y,radius:150,label:'GHOST RAMP'};
  else if(b.bossKind==='black_entity')attack=choose<.64?{kind:'void_well',warn:1.05,x:tx,y:ty,radius:270,label:'NULL GRAVITY'}:{kind:'blink_strike',warn:.62,x:tx,y:ty,fromX:b.x,fromY:b.y,radius:145,label:'ENTITY SHIFT'};
  else attack=choose<.56?{kind:'memory_cross',warn:1.0,x:tx,y:ty,range:650,width:58,label:'MEMORY CROSS'}:{kind:'shard_burst',warn:.72,x:b.x,y:b.y,radius:520,label:'REMEMBRANCE BURST'};
  attack.phase=phase;b.pendingAttack=attack;
  v1BossActionSnapshot(room,b,attack.kind,{...attack,phase:'warn',color:b.color,duration:.7});
}
function v1ExecuteBossAttack(room,b,attack){
  if(!attack)return;
  const kind=attack.kind;
  if(kind==='laser_sweep')v1BossHitBeam(room,b,attack.angle,attack.range,attack.width,attack.phase===2?32:26,'administrative_beam');
  else if(kind==='admin_pulse')v1BossHitCircle(room,b,b.x,b.y,attack.radius,attack.phase===2?25:20,'access_denied');
  else if(kind==='bio_bloom')v1BossHitCircle(room,b,attack.x,attack.y,attack.radius,attack.phase===2?29:23,'telomere_bloom');
  else if(kind==='heal'){b.hp=Math.min(b.maxHp,b.hp+b.maxHp*(attack.phase===2?.10:.07));}
  else if(kind==='rocket_barrage'){
    v1BossHitCircle(room,b,attack.x,attack.y,attack.radius,attack.phase===2?30:24,'rocket_barrage');
    const base=Math.atan2(attack.y-b.y,attack.x-b.x);
    for(let i=-2;i<=2;i++)broadcast(room.code,{type:'boss_projectile',bossId:b.id,boss:bossSnapshot(b),angle:base+i*.13,options:{kind:'rocket',speed:5.6,life:145,dmg:0,color:b.color,size:9,visualOnly:true,networkReplay:true,explode:true}});
  }else if(kind==='ghost_dash'||kind==='blink_strike'){
    const oldX=b.x,oldY=b.y,p=islandServerNearest?islandServerNearest(attack.x+rand(-75,75),attack.y+rand(-75,75),(b.r||48)+80):{x:attack.x,y:attack.y};b.x=p.x;b.y=p.y;
    v1BossHitCircle(room,b,b.x,b.y,attack.radius,attack.phase===2?28:22,kind);
    attack.fromX=oldX;attack.fromY=oldY;attack.x=b.x;attack.y=b.y;
  }else if(kind==='void_well')v1BossHitCircle(room,b,attack.x,attack.y,attack.radius,attack.phase===2?31:25,'void_well');
  else if(kind==='memory_cross'){
    for(const snap of livePlayerSnapshots(room)){if(clientIsInvincible(snap.client))continue;const dx=Math.abs(snap.x-attack.x),dy=Math.abs(snap.y-attack.y);if((dx<attack.width||dy<attack.width)&&dx<attack.range&&dy<attack.range)sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount:attack.phase===2?30:24,cause:'memory_cross'});}
  }else if(kind==='shard_burst'){
    const count=attack.phase===2?14:10;
    for(let i=0;i<count;i++)broadcast(room.code,{type:'boss_projectile',bossId:b.id,boss:bossSnapshot(b),angle:i/count*Math.PI*2,options:{kind:'memory',speed:6.2,life:120,dmg:0,color:b.color,size:7,visualOnly:true,networkReplay:true}});
    for(const snap of livePlayerSnapshots(room)){const d=Math.hypot(snap.x-b.x,snap.y-b.y),a=Math.atan2(snap.y-b.y,snap.x-b.x),step=Math.PI*2/count,error=Math.abs(((a+step/2)%step)-step/2);if(d<attack.radius&&error<.13)sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount:attack.phase===2?25:19,cause:'remembrance_burst'});}
  }
  v1BossActionSnapshot(room,b,kind,{...attack,phase:'fire',warn:0,color:b.color,duration:.55});
}

spawnSharedBoss=function(room,forcedId=null){
  if(['test','br','bossrush'].includes(room.mode))return null;
  if(room.bosses.some(b=>!b.dead))return null;
  const def=forcedId?(bossDefs.find(x=>x.id===forcedId)||bossDefs[0]):bossDefs[irand(0,bossDefs.length)];
  const p=typeof islandServerRandomPoint==='function'?islandServerRandomPoint((def.r||48)+90,null,600):{x:rand(-HALF_W+900,HALF_W-900),y:rand(-HALF_H+700,HALF_H-700)};
  const b={id:'boss_'+(++room.lastBossSerial)+'_'+id(3),bossKind:def.id,name:def.name,color:def.color,skin:def.skin,archetype:def.archetype,x:p.x,y:p.y,vx:0,vy:0,r:def.r,hp:def.hp,maxHp:def.hp,speed:def.speed,angle:rand(0,Math.PI*2),dead:false,fireCd:2.0,specialCd:rand(3.8,5.6),pendingAttack:null,spawnUntil:Date.now()+2400,attackName:'Materializing',desc:def.desc};
  room.bosses.push(b);broadcast(room.code,{type:'boss_event',action:'spawn',boss:bossSnapshot(b)});return b;
};
bossSnapshot=function(b){return{id:b.id,bossKind:b.bossKind,name:b.name,x:Math.round(b.x*10)/10,y:Math.round(b.y*10)/10,vx:Math.round((b.vx||0)*100)/100,vy:Math.round((b.vy||0)*100)/100,r:b.r,angle:b.angle,hp:Math.max(0,Math.round(b.hp*10)/10),maxHp:b.maxHp,color:b.color,skin:b.skin,archetype:b.archetype,dead:!!b.dead,desc:b.desc,spawnRemaining:Math.max(0,((b.spawnUntil||0)-Date.now())/1000),attackName:b.pendingAttack?.label||b.attackName||''};};
updateSharedBosses=function(room,dt){
  if(!room.matchStarted||['test','br','bossrush'].includes(room.mode))return;
  const now=Date.now();if(now>room.nextBossAt){spawnSharedBoss(room);room.nextBossAt=now+rand(70000,100000);}
  for(const b of room.bosses){
    if(b.dead)continue;
    if(now<(b.spawnUntil||0)){b.vx*=.82;b.vy*=.82;continue;}
    const target=nearestTargetForBoss(room,b);
    if(!target){b.vx*=.92;b.vy*=.92;continue;}
    const snap=target.snap,d=target.d;b.angle=Math.atan2(snap.y-b.y,snap.x-b.x);
    if(b.pendingAttack){b.pendingAttack.warn-=dt/1000;b.vx*=.84;b.vy*=.84;if(b.pendingAttack.warn<=0){const attack=b.pendingAttack;b.pendingAttack=null;v1ExecuteBossAttack(room,b,attack);b.specialCd=rand(4.4,6.8);}continue;}
    b.specialCd=Math.max(0,(b.specialCd||0)-dt/1000);
    if(b.specialCd<=0&&d<1150){v1QueueBossAttack(room,b,target);continue;}
    const tx=Math.cos(b.angle),ty=Math.sin(b.angle),desired=b.bossKind==='black_entity'?340:430;let mx=0,my=0;
    if(d>desired+80){mx=tx;my=ty;}else if(d<desired-120){mx=-tx;my=-ty;}else{mx=-Math.sin(b.angle)*.75;my=Math.cos(b.angle)*.75;}
    b.vx=b.vx*.90+mx*b.speed*.10;b.vy=b.vy*.90+my*b.speed*.10;b.fireCd-=dt/1000;
    if(b.fireCd<=0&&d<780){b.fireCd=rand(1.0,1.55);const shot={kind:'boss',speed:5.2,life:135,dmg:13,color:b.color,size:9,visualOnly:true,networkReplay:true};broadcast(room.code,{type:'boss_projectile',bossId:b.id,boss:bossSnapshot(b),angle:b.angle+rand(-.16,.16),options:shot});if(d<650&&Math.random()<.34)sendDamageToClient(snap.client,{type:'boss_hit',bossId:b.id,bossName:b.name,amount:13,cause:'boss_projectile'});}
    b.x+=b.vx*dt/16.6;b.y+=b.vy*dt/16.6;if(typeof islandServerConstrainObject==='function')islandServerConstrainObject(b,(b.r||48)+70);else{b.x=clamp(b.x,-HALF_W+80,HALF_W-80);b.y=clamp(b.y,-HALF_H+80,HALF_H-80);}
  }
  room.bosses=room.bosses.filter(b=>!b.removeAt||Date.now()<b.removeAt);
};

function v1UpdateSharedFragmentStorms(room){
  const storms=room.v1FragmentStorms||[];const now=Date.now();
  for(let i=storms.length-1;i>=0;i--){const s=storms[i];if(now>=s.expiresAt){storms.splice(i,1);continue;}if(now<s.nextAt)continue;s.nextAt=now+220;const density=s.evolved?3:2;for(let n=0;n<density;n++){const a=rand(0,Math.PI*2),r=Math.sqrt(Math.random())*s.radius;spawnSharedFragment(room,Math.random()<.35?'natural':'xp',s.x+Math.cos(a)*r,s.y+Math.sin(a)*r);}if(Math.random()<.08)spawnSharedFragment(room,'ability',s.x+rand(-s.radius*.65,s.radius*.65),s.y+rand(-s.radius*.65,s.radius*.65));}
}
const v1OriginalUpdateSharedWorld=updateSharedWorld;
updateSharedWorld=function(room,dt){const result=v1OriginalUpdateSharedWorld(room,dt);v1UpdateSharedFragmentStorms(room);return result;};
const v1OriginalHandleMessage=handleMessage;
handleMessage=function(client,msg){
  if(msg?.type==='ability_event'&&safeToken(msg.abilityId,48)==='fragment_storm'&&client.inMatch&&client.room){const room=rooms.get(client.room);const now=Date.now();if(room&&now-(client.v1LastFragmentStormAt||0)>1500){client.v1LastFragmentStormAt=now;const snap=client.snapshot||{};room.v1FragmentStorms=room.v1FragmentStorms||[];room.v1FragmentStorms.push({ownerId:client.id,x:finiteNumber(msg.x,snap.x||0,-HALF_W,HALF_W),y:finiteNumber(msg.y,snap.y||0,-HALF_H,HALF_H),radius:msg.evolved?300:210,evolved:!!msg.evolved,nextAt:now,expiresAt:now+(msg.evolved?7000:4000)});room.v1FragmentStorms=room.v1FragmentStorms.slice(-8);}}
  return v1OriginalHandleMessage(client,msg);
};
console.log('[Fragment.io] Boss abilities, bot score, curse, and ability sync patch enabled.');



// -----------------------------------------------------------------------------
// v1.0 roster, social, and Battle Royale release overhaul
// -----------------------------------------------------------------------------
const releaseBaseFragCountsForMode=fragCountsForMode;
fragCountsForMode=function(mode,playerCount=2){
  if(mode==='br'){
    const real=Math.max(1,Math.floor(Number(playerCount)||1));
    return{
      xp:96+Math.min(24,real),
      natural:26+Math.min(8,Math.floor(real/4)),
      ability:7,
      evo:4,
      world:1,
      cursed:1
    };
  }
  return releaseBaseFragCountsForMode(mode,playerCount);
};

function releaseUpdateBrBotEvolution(room){
  if(room?.mode!=='br')return;
  const now=Date.now();
  const combatStart=Number(room.brCombatStartsAt)||Number(room.startedAt)||now;
  const elapsed=Math.max(0,(now-combatStart)/1000);
  for(const bot of room.bots){
    if(!bot||bot.dead)continue;
    const path=BR_SERVER_BOT_PATHS[Number(bot.brPathIndex)||0]||BR_SERVER_BOT_PATHS[0];
    const scoreLevel=Math.max(Number(bot.level)||1,1+Math.floor((Number(bot.score)||0)/950));
    let stage=0;
    if(elapsed>=105||scoreLevel>=4)stage=1;
    if(elapsed>=260||scoreLevel>=9)stage=2;
    if(elapsed>=480||scoreLevel>=15)stage=3;
    stage=Math.min(stage,path.length-1);
    if(stage!==bot.brEvolutionStage||bot.archetype!==path[stage]){
      bot.brEvolutionStage=stage;
      bot.archetype=path[stage];
      bot.bodyColor=colors[(Number(bot.brPathIndex)||0)%colors.length];
    }
  }
}
const releaseBaseUpdateServerBots=updateServerBots;
updateServerBots=function(room,dt){
  if(room?.mode==='br'&&Date.now()<(Number(room.brCombatStartsAt)||0)){
    const now=Date.now();
    if(now-(room.lastBotBroadcast||0)>250){
      room.lastBotBroadcast=now;
      broadcast(room.code,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)});
    }
    return;
  }
  releaseUpdateBrBotEvolution(room);
  return releaseBaseUpdateServerBots(room,dt);
};

console.log('[Fragment.io] Friend requests, full bot rosters, squad completion, and slower Battle Royale enabled.');



// -----------------------------------------------------------------------------
// Fragment.io v1.0 beta release-candidate hardening
// - stronger chat moderation and spam protection
// - team-only quick pings with server-side anti-spam
// - profile friend-request endpoint
// - foreground resynchronization after background-tab throttling
// -----------------------------------------------------------------------------
const V11_CHAT_TERMS=Object.freeze([
  'fuck','shit','bitch','asshole','cunt','nigger','nigga','faggot',
  'retard','kys','killyourself','whore','slut'
]);
const V11_LEET_MAP=Object.freeze({
  '0':'o','1':'i','2':'z','3':'e','4':'a','5':'s','6':'g','7':'t','8':'b','9':'g',
  '@':'a','$':'s','!':'i','|':'i','+':'t'
});
const V11_HOMOGLYPH_MAP=Object.freeze({
  'а':'a','е':'e','о':'o','р':'p','с':'c','х':'x','у':'y','і':'i','ј':'j',
  'ɑ':'a','е':'e','ο':'o','ρ':'p','ϲ':'c','χ':'x','υ':'y'
});
function v11ChatNormalize(value){
  return String(value||'')
    .normalize('NFKD')
    .replace(/[\u0300-\u036f]/g,'')
    .toLowerCase()
    .split('')
    .map(character=>V11_LEET_MAP[character]||V11_HOMOGLYPH_MAP[character]||character)
    .join('')
    .replace(/(.)\1{2,}/g,'$1')
    .replace(/[^a-z0-9]+/g,'');
}
function v11ChatTermMatch(normalized){
  if(!normalized)return false;
  return V11_CHAT_TERMS.some(term=>{
    if(normalized===term)return true;
    if(term==='kys')return normalized==='kys';
    if(term==='killyourself')return normalized.includes(term);
    return normalized===term+'s'
      ||normalized===term+'es'
      ||normalized===term+'ing'
      ||normalized===term+'ed'
      ||normalized===term+'er';
  });
}
function v11ModerateChatText(input){
  const clean=String(input||'')
    .replace(/[<>\u0000-\u001f\u007f]/g,'')
    .replace(/\s+/g,' ')
    .trim()
    .slice(0,120);
  if(!clean)return'';

  let censored=false;
  const parts=clean.split(/(\s+)/).map(part=>{
    if(/^\s+$/.test(part))return part;
    const normalized=v11ChatNormalize(part);
    if(v11ChatTermMatch(normalized)){
      censored=true;
      return'•••';
    }
    return part;
  });

  const compact=v11ChatNormalize(clean);
  if(!censored&&V11_CHAT_TERMS.some(term=>term.length>=3&&compact.includes(term))){
    return'[message filtered]';
  }
  return parts.join('').slice(0,120);
}
function v11ChatLooksLikeSpam(body){
  const clean=String(body||'').trim();
  if(/(.)\1{10,}/i.test(clean))return true;
  const words=clean.toLowerCase().split(/\s+/).filter(Boolean);
  if(words.length>=5&&new Set(words).size<=2)return true;
  if((clean.match(/[!?]/g)||[]).length>14)return true;
  return false;
}
function v11ChatReject(client,message){
  send(client,{type:'chat',name:'SERVER',msg:message});
}
function v11HandleChat(client,msg){
  if(!client.room)return;
  const room=rooms.get(client.room);
  if(!room)return;

  const now=Date.now();
  const raw=String(msg.msg||'').replace(/[<>\u0000-\u001f\u007f]/g,'').replace(/\s+/g,' ').trim().slice(0,120);
  if(!raw)return;

  if(now<(client.moderationMutedUntil||0)){
    const seconds=Math.max(1,Math.ceil((client.moderationMutedUntil-now)/1000));
    v11ChatReject(client,`You are muted for another ${seconds}s.`);
    return;
  }
  if(now<(client.chatMutedUntil||0)){
    const seconds=Math.max(1,Math.ceil((client.chatMutedUntil-now)/1000));
    v11ChatReject(client,`Chat cooldown: wait ${seconds}s.`);
    return;
  }

  const wait=1800-(now-(client.lastChatAt||0));
  if(wait>0){
    v11ChatReject(client,`Chat cooldown: wait ${(wait/1000).toFixed(1)}s.`);
    return;
  }

  const fingerprint=v11ChatNormalize(raw);
  client.v11ChatHistory=(client.v11ChatHistory||[]).filter(entry=>now-entry.at<30000);
  client.v11ChatShort=(client.v11ChatShort||[]).filter(at=>now-at<10000);
  client.v11ChatLong=(client.v11ChatLong||[]).filter(at=>now-at<30000);

  const duplicate=client.v11ChatHistory.some(entry=>entry.fingerprint===fingerprint&&now-entry.at<12000);
  if(duplicate){
    v11ChatReject(client,'Duplicate or near-duplicate message blocked.');
    return;
  }
  if(v11ChatLooksLikeSpam(raw)){
    client.v11ChatSpamStrikes=(client.v11ChatSpamStrikes||0)+1;
    const duration=[12,35,120][Math.min(2,client.v11ChatSpamStrikes-1)];
    client.chatMutedUntil=now+duration*1000;
    v11ChatReject(client,`Chat spam detected. Muted for ${duration} seconds.`);
    return;
  }
  if(client.v11ChatShort.length>=4||client.v11ChatLong.length>=8){
    client.v11ChatSpamStrikes=(client.v11ChatSpamStrikes||0)+1;
    const duration=[15,60,300][Math.min(2,client.v11ChatSpamStrikes-1)];
    client.chatMutedUntil=now+duration*1000;
    client.v11ChatShort=[];
    client.v11ChatLong=[];
    v11ChatReject(client,`Chat spam detected. Muted for ${duration} seconds.`);
    return;
  }

  const body=v11ModerateChatText(raw);
  if(!body)return;

  client.lastChatAt=now;
  client.lastChatBody=fingerprint;
  client.v11ChatShort.push(now);
  client.v11ChatLong.push(now);
  client.v11ChatHistory.push({fingerprint,at:now});
  client.v11ChatHistory=client.v11ChatHistory.slice(-12);

  broadcast(room.code,{
    type:'chat',
    name:client.name,
    msg:body,
    accountRole:publicAccountRole(client.accountRole),
    userId:client.userId||''
  });
}
function v11QuickPingRecipient(sender,recipient,party){
  if(!sender||!recipient||sender.room!==recipient.room||!recipient.inMatch)return false;
  if(sender===recipient)return true;
  if(sameCombatTeam(sender.serverTeam,recipient.serverTeam))return true;
  return !!(party&&sender.userId&&recipient.userId&&party.members.has(sender.userId)&&party.members.has(recipient.userId));
}
function v11HandleQuickPing(client,msg){
  if(!client.authenticated||!client.room||!client.inMatch)return;
  const room=rooms.get(client.room);
  if(!room)return;

  const now=Date.now();
  if(now<(client.v11PingMutedUntil||0)){
    const seconds=Math.max(1,Math.ceil((client.v11PingMutedUntil-now)/1000));
    send(client,{type:'social_notice',message:`Quick Ping muted for another ${seconds}s.`});
    return;
  }

  const kind=safeToken(msg.kind,24);
  if(!['enemy','fragment','boss','retreat','group','solarbum'].includes(kind))return;

  const cooldown=3000-(now-(client.lastPartyPingAt||0));
  if(cooldown>0){
    send(client,{type:'social_notice',message:`Quick Ping cooldown: wait ${(cooldown/1000).toFixed(1)}s.`});
    return;
  }

  client.v11PingTimes=(client.v11PingTimes||[]).filter(at=>now-at<15000);
  const repeated=kind===(client.v11LastPingKind||'')&&now-(client.v11LastPingKindAt||0)<6000;
  if(repeated){
    send(client,{type:'social_notice',message:'Repeated Quick Ping blocked.'});
    return;
  }
  if(client.v11PingTimes.length>=4){
    client.v11PingSpamStrikes=(client.v11PingSpamStrikes||0)+1;
    const duration=[15,45,120][Math.min(2,client.v11PingSpamStrikes-1)];
    client.v11PingMutedUntil=now+duration*1000;
    client.v11PingTimes=[];
    send(client,{type:'social_notice',message:`Quick Ping spam detected. Muted for ${duration} seconds.`});
    return;
  }

  client.lastPartyPingAt=now;
  client.v11LastPingKind=kind;
  client.v11LastPingKindAt=now;
  client.v11PingTimes.push(now);

  const payload={
    type:'party_ping',
    kind,
    x:finiteNumber(msg.x,client.snapshot?.x||0,-HALF_W,HALF_W),
    y:finiteNumber(msg.y,client.snapshot?.y||0,-HALF_H,HALF_H),
    sourceName:client.name,
    userId:client.userId,
    sourceClientId:client.id
  };
  const party=partyForClient(client);
  for(const recipient of room.clients){
    if(v11QuickPingRecipient(client,recipient,party))send(recipient,payload);
  }
}
async function v11SendFriendRequestByUserId(client,msg){
  if(!client.authenticated||!client.userId)throw new Error('Login before sending friend requests.');
  const targetUserId=cleanUserId(msg.targetUserId);
  if(!targetUserId||targetUserId===client.userId)throw new Error('Invalid player.');
  const rows=await supabaseAdminRequest(
    '/rest/v1/profiles?id=eq.'+encodeURIComponent(targetUserId)
    +'&select=id,username,friend_code&limit=1',
    {method:'GET'}
  );
  const target=Array.isArray(rows)?rows[0]:null;
  if(!target?.friend_code)throw new Error('That account is not available for friend requests.');
  return sendFriendRequestByCode(client,{friendCode:target.friend_code});
}
function v11SendStateResync(client){
  if(!client.room)return;
  const room=rooms.get(client.room);
  if(!room)return;
  const peers=peersFor(client);
  send(client,{type:'peers',peers,immediate:true});
  send(client,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot),immediate:true});
  sendSharedState(client,room,true);
  send(client,{type:'resync_complete',serverNow:Date.now(),mode:room.mode});
}

const v11BaseHandleMessage=handleMessage;
handleMessage=function(client,msg){
  if(!msg||typeof msg!=='object')return v11BaseHandleMessage(client,msg);

  if(msg.type==='chat'){
    v11HandleChat(client,msg);
    return;
  }
  if(msg.type==='party_ping'){
    v11HandleQuickPing(client,msg);
    return;
  }
  if(msg.type==='friend_request_send_user'){
    v11SendFriendRequestByUserId(client,msg)
      .catch(error=>send(client,{type:'social_error',message:error.message||'Could not send friend request.'}));
    return;
  }
  if(msg.type==='state_resync'){
    v11SendStateResync(client);
    return;
  }

  return v11BaseHandleMessage(client,msg);
};

console.log('[Fragment.io] Beta release-candidate chat, ping, friend, and resync hardening enabled.');



// -----------------------------------------------------------------------------
// Fragment.io v1.0 friend-request action acknowledgement patch
// -----------------------------------------------------------------------------
async function v12FriendRequestAction(client,msg,action){
  if(!client?.authenticated||!client.userId){
    throw new Error('Login before managing friend requests.');
  }

  const requestIdText=String(msg?.requestId??'').trim();
  if(!/^\d+$/.test(requestIdText)){
    throw new Error('Invalid friend request.');
  }
  const requestId=Number(requestIdText);
  if(!Number.isSafeInteger(requestId)||requestId<1){
    throw new Error('Invalid friend request.');
  }

  if(action==='accept'){
    await acceptFriendRequest(client,{requestId});
  }else if(action==='decline'){
    await closeFriendRequest(client,{requestId},'declined');
  }else if(action==='cancel'){
    await closeFriendRequest(client,{requestId},'cancelled');
  }else{
    throw new Error('Invalid friend-request action.');
  }

  send(client,{
    type:'friend_request_action_result',
    ok:true,
    action,
    requestId
  });

  // Always return a fresh request list to the acting session immediately,
  // even if another refresh sent by the shared helper is still in flight.
  await sendFriendRequestState(client);
}

const v12BaseHandleMessage=handleMessage;
handleMessage=function(client,msg){
  if(msg?.type==='friend_request_accept'){
    v12FriendRequestAction(client,msg,'accept').catch(error=>{
      send(client,{
        type:'friend_request_action_result',
        ok:false,
        action:'accept',
        requestId:String(msg?.requestId??''),
        message:error.message||'Could not accept friend request.'
      });
    });
    return;
  }
  if(msg?.type==='friend_request_decline'){
    v12FriendRequestAction(client,msg,'decline').catch(error=>{
      send(client,{
        type:'friend_request_action_result',
        ok:false,
        action:'decline',
        requestId:String(msg?.requestId??''),
        message:error.message||'Could not decline friend request.'
      });
    });
    return;
  }
  if(msg?.type==='friend_request_cancel'){
    v12FriendRequestAction(client,msg,'cancel').catch(error=>{
      send(client,{
        type:'friend_request_action_result',
        ok:false,
        action:'cancel',
        requestId:String(msg?.requestId??''),
        message:error.message||'Could not cancel friend request.'
      });
    });
    return;
  }
  return v12BaseHandleMessage(client,msg);
};

console.log('[Fragment.io] Friend request accept, decline, and cancel acknowledgements enabled.');



// -----------------------------------------------------------------------------
// Fragment.io v1.0 performance / BR timer / friend dedupe / Developer Remnant
// -----------------------------------------------------------------------------
const V13_MAX_REMNANT_BALANCE=2000000000;
const V13_MAX_REMNANT_GRANT=2000000000;

async function v13ResolveRemnantTarget(msg){
  const direct=cleanUserId(msg?.targetUserId);
  if(direct){
    const rows=await supabaseAdminRequest(
      '/rest/v1/profiles?id=eq.'+encodeURIComponent(direct)
      +'&select=id,username,friend_code&limit=1',
      {method:'GET'}
    );
    const profile=Array.isArray(rows)?rows[0]:null;
    if(!profile)throw new Error('That account does not exist.');
    return profile;
  }

  const reference=String(msg?.targetRef||'')
    .trim()
    .toUpperCase()
    .replace(/[^A-Z0-9-]/g,'')
    .slice(0,36);
  if(!reference)throw new Error('Choose a player or enter a Friend Code.');

  const asUserId=cleanUserId(reference);
  if(asUserId){
    const rows=await supabaseAdminRequest(
      '/rest/v1/profiles?id=eq.'+encodeURIComponent(asUserId)
      +'&select=id,username,friend_code&limit=1',
      {method:'GET'}
    );
    const profile=Array.isArray(rows)?rows[0]:null;
    if(!profile)throw new Error('That account does not exist.');
    return profile;
  }

  const rows=await supabaseAdminRequest(
    '/rest/v1/profiles?friend_code=eq.'+encodeURIComponent(reference)
    +'&select=id,username,friend_code&limit=1',
    {method:'GET'}
  );
  const profile=Array.isArray(rows)?rows[0]:null;
  if(!profile)throw new Error('No account uses that Friend Code.');
  return profile;
}

async function v13DeveloperGrantRemnant(client,msg){
  if(!requireDeveloper(client))return;

  const amountText=String(msg?.amount??'').replace(/[,_\s]/g,'');
  if(!/^\d+$/.test(amountText))throw new Error('Enter a whole positive Remnant amount.');
  const amount=Number(amountText);
  if(!Number.isSafeInteger(amount)||amount<1||amount>V13_MAX_REMNANT_GRANT){
    throw new Error('The grant must be between 1 and 2,000,000,000 Remnant.');
  }

  const target=await v13ResolveRemnantTarget(msg);
  const saveRows=await supabaseAdminRequest(
    '/rest/v1/player_data?user_id=eq.'+encodeURIComponent(target.id)
    +'&select=user_id,remnant&limit=1',
    {method:'GET'}
  );
  const existing=Array.isArray(saveRows)?saveRows[0]:null;
  const oldBalance=Math.max(0,Math.floor(Number(existing?.remnant)||0));

  if(oldBalance>V13_MAX_REMNANT_BALANCE-amount){
    throw new Error('That grant would exceed the 2,000,000,000 Remnant account limit.');
  }
  const newBalance=oldBalance+amount;

  if(existing){
    await supabaseAdminRequest(
      '/rest/v1/player_data?user_id=eq.'+encodeURIComponent(target.id),
      {
        method:'PATCH',
        headers:{Prefer:'return=minimal'},
        body:JSON.stringify({remnant:newBalance})
      }
    );
  }else{
    await supabaseAdminRequest('/rest/v1/player_data',{
      method:'POST',
      headers:{Prefer:'return=minimal'},
      body:JSON.stringify({user_id:target.id,remnant:newBalance})
    });
  }

  await insertModerationAction({
    moderator:client,
    targetUserId:target.id,
    targetName:target.username||'Player',
    action:'remnant_grant',
    reason:'Granted '+amount.toLocaleString('en-US')+' Remnant.',
    roomCode:onlineClientForUser(target.id)?.room||null,
    metadata:{amount,oldBalance,newBalance,friendCode:target.friend_code||null}
  });

  const payload={
    type:'developer_remnant_balance',
    amount,
    balance:newBalance,
    targetUserId:target.id,
    targetName:target.username||'Player',
    grantedBy:client.profile?.username||client.name||'Developer'
  };
  for(const session of allOnlineClientsForUser(target.id))send(session,payload);

  send(client,{
    type:'developer_remnant_result',
    ok:true,
    amount,
    balance:newBalance,
    targetUserId:target.id,
    targetName:target.username||'Player',
    friendCode:target.friend_code||''
  });
}

const v13BaseHandleMessage=handleMessage;
handleMessage=function(client,msg){
  if(msg?.type==='developer_grant_remnant'){
    v13DeveloperGrantRemnant(client,msg)
      .catch(error=>send(client,{
        type:'developer_remnant_result',
        ok:false,
        message:error.message||'Could not grant Remnant.'
      }));
    return;
  }
  return v13BaseHandleMessage(client,msg);
};

console.log('[Fragment.io] Secure Developer Remnant grants enabled.');

