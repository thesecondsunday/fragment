#!/usr/bin/env node
'use strict';

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
const SUPPORTED_MODES = new Set(['normal','test','duo','squad','teams','br','bossrush','pvp']);
const DROPPABLE_PACKET_TYPES = new Set(['peer_state','bots_state','fragments_state','world_state','bosses_state']);
const rooms = new Map();
const clients = new Set();

function id(bytes = 8){ return crypto.randomBytes(bytes).toString('hex'); }
function cleanRoom(v){ return String(v || '').trim().toUpperCase().replace(/[^A-Z0-9-]/g, '').slice(0,18) || crypto.randomBytes(3).toString('hex').toUpperCase(); }
function safeName(v){ return String(v || 'Player').replace(/[<>]/g,'').slice(0,24) || 'Player'; }
function cleanMode(v){
  const mode = String(v || 'normal').toLowerCase();
  return SUPPORTED_MODES.has(mode) ? mode : 'normal';
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
    const list=[...room.clients];
    const idx=Math.max(0,list.indexOf(client));
    return idx % 2 === 0 ? 'blue' : 'red';
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
  const maxHp = finiteNumber(raw.maxHp, finiteNumber(previous?.maxHp,100,1,100000), 1, 100000);
  const dead = !!raw.dead;
  if((!previous && !dead) || (previous?.dead && !dead)){
    client.spawnProtectedUntil = Date.now() + 2600;
  }
  const snap = {...raw};
  snap.id = client.id;
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
  snap.archetype = safeToken(raw.archetype || 'starter',48) || 'starter';
  snap.bodyColor = /^#[0-9a-fA-F]{3,8}$/.test(String(raw.bodyColor||'')) ? String(raw.bodyColor) : '#5d8cff';
  snap.skinKind = safeToken(raw.skinKind || 'circle',32) || 'circle';
  snap.spawnInvincible = finiteNumber(raw.spawnInvincible,0,0,20);
  snap.reflect = finiteNumber(raw.reflect,0,0,30);
  snap.bulletEater = finiteNumber(raw.bulletEater,0,0,30);
  snap.invisible = finiteNumber(raw.invisible,0,0,30);
  snap.abilities = Array.isArray(raw.abilities) ? raw.abilities.slice(0,5).map(v=>v==null?null:safeToken(v,48)) : [];
  return snap;
}

function makeRoom(code){
  return {
    code,
    clients:new Set(),
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
    createdAt:Date.now()
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
function removeFromRoom(client){
  if(!client.room) return;
  const room = rooms.get(client.room);
  if(room){
    room.clients.delete(client);
    broadcast(client.room, {type:'peer_left', clientId:client.id, name:client.name}, client);
    chooseLeader(room);
    if(room.clients.size === 0){ rooms.delete(client.room); }
    else { broadcastLobby(room); }
  }
  client.room = null;
  client.ready = false;
  client.inMatch = false;
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
const colors = ['#ff775d','#6a7cf7','#53b07b','#ffcf58','#76d7ff','#cb80ff','#d84a4a','#9aa9b8'];
function botCountForMode(mode){
  // One authoritative bot roster per room, not per player.
  // Lower counts improve readability and significantly reduce network/render load.
  if(mode === 'pvp' || mode === 'bossrush') return 0;
  if(mode === 'test') return 6;
  if(mode === 'duo') return 6;
  if(mode === 'squad') return 8;
  if(mode === 'teams') return 10;
  if(mode === 'br') return 12;
  return 7;
}
function teamForBot(mode, i, count){
  if(mode === 'teams') return i < Math.ceil(count/2) ? 'blue' : 'red';
  if(['duo','squad','test'].includes(mode)) return 'red';
  return 'neutral';
}
function spawnServerBots(room){
  room.bots = [];
  const count = botCountForMode(room.mode);
  for(let i=0;i<count;i++){
    const team = teamForBot(room.mode, i, count);
    const passive = room.mode === 'test';
    const namePrefix = room.mode === 'br' ? 'BR ' : room.mode === 'teams' ? (team === 'blue' ? 'Blue ' : 'Red ') : room.mode === 'squad' ? 'Enemy ' : '';
    const point = room.mode === 'test'
      ? {x:((i % 4) - 1.5) * 260, y:(Math.floor(i / 4) - 1) * 230}
      : randomArenaPoint(720,360);
    const roam = randomArenaPoint(620,260);
    const bot = {
      id:'bot_' + id(5),
      name: passive ? `Dummy ${String(i+1).padStart(2,'0')}` : `${namePrefix}${botNames[i % botNames.length]}-${String(i+1).padStart(2,'0')}`,
      x:point.x, y:point.y,
      vx:0, vy:0, r:18, angle:rand(0, Math.PI*2),
      hp: passive ? 280 : 115, maxHp: passive ? 280 : 115,
      score:0, frags:0, level:1,
      team, ally:team === 'blue', passive,
      archetype: archetypes[i % archetypes.length],
      bodyColor: passive ? '#7fd8ff' : colors[i % colors.length],
      fireCd:rand(1.3,2.1), think:0, strafe:Math.random()<0.5 ? -1 : 1,
      aimError:rand(-0.10,0.10), dodge:rand(.75,1.25), confidence:rand(.75,1.22),
      meleeCd:rand(.9,1.5), lastTargetId:null, targetLockUntil:0,
      personality:['duelist','hunter','scavenger','coward','roamer'][i%5],
      roamX:roam.x, roamY:roam.y,
      spawnGraceUntil:Date.now()+rand(1700,2600),
      dead:false, respawnAt:0, lastHitBy:null
    };
    room.bots.push(bot);
  }
}
function startMatch(room){
  room.matchStarted = true;
  room.matchId++;
  assignRoomTeams(room);
  const now=Date.now();
  for(const c of room.clients){
    c.inMatch = true;
    c.spawnProtectedUntil = now + 2600;
    if(c.snapshot) c.snapshot.team = c.serverTeam;
  }
  spawnServerBots(room);
  initSharedWorld(room);
  const botsState = {type:'bots_state', mode:room.mode, bots:room.bots.map(botSnapshot), immediate:true};
  broadcast(room.code, {type:'match_start', mode:room.mode, matchId:room.matchId, startedAt:now});
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
function botCanTarget(bot, target){
  if(!target || target.dead) return false;
  if(sameCombatTeam(bot.team, target.team)) return false;
  if(target.kind === 'player' && clientIsInvincible(target.client)) return false;
  return true;
}
function nearestTargetForBot(room, bot){
  const now=Date.now();
  const candidates=[];
  for(const snap of livePlayerSnapshots(room)){
    candidates.push({
      kind:'player',
      id:snap.client.id,
      key:'player:'+snap.client.id,
      name:snap.name||snap.client.name,
      client:snap.client,
      x:snap.x||0, y:snap.y||0, vx:snap.vx||0, vy:snap.vy||0,
      hp:snap.hp||1, maxHp:snap.maxHp||1,
      team:snap.client.serverTeam||snap.team||'neutral',
      dead:!!snap.dead,
      human:true
    });
  }
  for(const other of room.bots){
    if(other===bot || other.dead) continue;
    candidates.push({
      kind:'bot',
      id:other.id,
      key:'bot:'+other.id,
      name:other.name,
      bot:other,
      x:other.x, y:other.y, vx:other.vx||0, vy:other.vy||0,
      hp:other.hp, maxHp:other.maxHp,
      team:other.team||'neutral',
      dead:!!other.dead,
      human:false
    });
  }

  const locked = candidates.find(t=>t.key===bot.lastTargetId);
  if(locked && bot.targetLockUntil>now && botCanTarget(bot,locked)){
    const d=dist(bot,locked);
    if(d<1250) return {snap:locked,d};
  }

  let best=null, bestScore=-Infinity;
  for(const target of candidates){
    if(!botCanTarget(bot,target)) continue;
    const d=dist(bot,target);
    if(d>1220) continue;
    const hpRatio=clamp((target.hp||1)/Math.max(1,target.maxHp||1),0,1);
    let assigned=0;
    for(const other of room.bots){
      if(other!==bot && !other.dead && other.lastTargetId===target.key) assigned++;
    }
    let score = -d*.43 + (1-hpRatio)*165 - assigned*62;
    score += target.kind==='bot' ? 46 : 8;
    if(bot.lastHitBy===target.id) score += 240;
    if(d<300) score += 74;
    if(bot.personality==='hunter') score += (1-hpRatio)*90;
    if(bot.personality==='scavenger' && hpRatio>.62) score -= 85;
    if(bot.personality==='coward' && d<260 && target.hp>bot.hp) score -= 150;
    if(score>bestScore){ bestScore=score; best=target; }
  }
  if(!best) return null;
  bot.lastTargetId=best.key;
  bot.targetLockUntil=now+rand(850,1750);
  return {snap:best,d:dist(bot,best)};
}
function killServerBot(room, bot, source){
  if(!bot || bot.dead) return;
  bot.dead=true;
  bot.hp=0;
  bot.respawnAt=Date.now()+(room.mode==='br'?999999999:3200);
  bot.score=0;
  bot.lastTargetId=null;

  const dropCount=room.mode==='br'?8:11;
  spawnDeathFragmentBurst(room,bot.x,bot.y,dropCount,'bot_death',.26);

  if(source?.kind==='player' && source.client){
    send(source.client,{type:'bot_award',botId:bot.id,botName:bot.name,xp:40,score:250});
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
function deliverBotDamage(room, attacker, target, amount, cause){
  if(!target || !botCanTarget(attacker,target)) return false;
  if(target.kind==='player'){
    return sendDamageToClient(target.client,{
      type:'bot_hit',
      botId:attacker.id,
      botName:attacker.name,
      amount,
      cause
    });
  }
  if(target.kind==='bot'){
    return damageServerBot(room,target.bot,amount,{kind:'bot',id:attacker.id,name:attacker.name,bot:attacker});
  }
  return false;
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

        if(bot.fireCd<=0 && target.d<720){
          const rapid=['bullet_storm','machine','minigunner'].includes(bot.archetype);
          const long=['deadeye','solar_lance','sniper'].includes(bot.archetype);
          bot.fireCd=rapid?rand(.52,.78):long?rand(1.05,1.5):rand(.78,1.15);

          const spread=long?rand(-.055,.055):rapid?rand(-.14,.14):rand(-.10,.10);
          const shotAngle=ang+spread+bot.aimError*.35;
          const shot={
            kind:'basic',
            speed:long?8.7:7.6,
            life:long?112:96,
            dmg:long?9:rapid?4.2:6.2,
            color:bot.bodyColor,
            size:rapid?4:5,
            visualOnly:true,
            networkReplay:true
          };
          broadcast(room.code,{type:'bot_projectile',botId:bot.id,bot:botSnapshot(bot),angle:shotAngle,options:shot,serial:++room.lastShotSerial});

          const trueAngle=Math.atan2(t.y-bot.y,t.x-bot.x);
          const error=Math.abs(angleDiff(shotAngle,trueAngle));
          const distanceAccuracy=clamp(1-target.d/900,.08,.72);
          const hitChance=clamp((long?.34:rapid?.22:.28)+distanceAccuracy*.38-error*.92,.08,.68)*bot.confidence;
          if(error<.30 && Math.random()<hitChance) deliverBotDamage(room,bot,t,shot.dmg,'projectile');
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
  if(mode==='pvp') return {xp:105+extra*8,natural:32+extra*2,ability:8+Math.min(3,extra),evo:5+Math.min(2,extra),world:1,cursed:2};
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
    f.core = extra || coreIds[irand(0, coreIds.length)]; f.r=12;
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
  for(let i=0;i<safeCount;i++){
    const a=rand(0,Math.PI*2);
    const radius=Math.sqrt(Math.random())*rand(38,115);
    const kind=i>0 && i%8===0 ? 'natural' : 'xp';
    spawned.push(spawnSharedFragment(room,kind,x+Math.cos(a)*radius,y+Math.sin(a)*radius));
  }
  if(abilityChance>0 && Math.random()<abilityChance){
    spawned.push(spawnSharedFragment(room,'ability',x+rand(-55,55),y+rand(-55,55)));
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
  room.nextBossAt = ['pvp','test','br','bossrush'].includes(room.mode) ? 9999999999999 : Date.now()+rand(24000,36000);
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

  if(room.fragments.length>235){
    room.fragments.splice(0,room.fragments.length-235);
  }
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
  if(['pvp','test','br','bossrush'].includes(room.mode)) return null;
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
  if(!room.matchStarted || ['pvp','test','br','bossrush'].includes(room.mode)) return;
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
  }else if(now > room.world.nextAt && !['pvp','test','br'].includes(room.mode)){
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
      if(typeof value==='number' && Number.isFinite(value)) out[key]=clamp(value,-100000,100000);
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
function handleMessage(client, msg){
  if(typeof msg !== 'object' || !msg) return;
  client.lastSeen=Date.now();

  if(msg.type === 'join'){
    removeFromRoom(client);
    const room=getRoom(msg.room);
    client.room=room.code;
    client.name=safeName(msg.name);
    client.mode=cleanMode(msg.mode);
    client.ready=false;
    client.inMatch=false;
    client.snapshot=null;
    client.spawnProtectedUntil=Date.now()+2600;
    if(room.clients.size===0){
      room.mode=client.mode;
      room.matchStarted=false;
      room.bots=[]; room.fragments=[]; room.bosses=[]; room.terrainFeatures=[]; room.hotZone=null;
      room.nextTerrainAt=Date.now()+9000;
      room.nextHotZoneAt=Date.now()+16000;
      room.world={mode:null,timer:0,zones:[],nextAt:Date.now()+22000};
      room.nextBossAt=Date.now()+32000;
    }
    room.clients.add(client);
    chooseLeader(room);
    assignRoomTeams(room);
    send(client,{type:'welcome',clientId:client.id,room:room.code});
    const peers=peersFor(client);
    if(peers.length) send(client,{type:'peers',peers});
    broadcast(room.code,{type:'peer_joined',clientId:client.id,name:client.name,mode:room.mode},client);
    broadcastLobby(room);
    if(room.matchStarted){
      client.inMatch=true;
      client.spawnProtectedUntil=Date.now()+3000;
      send(client,{type:'match_start',mode:room.mode,matchId:room.matchId,startedAt:Date.now(),lateJoin:true});
      send(client,{type:'bots_state',mode:room.mode,bots:room.bots.map(botSnapshot)});
      sendSharedState(client,room,true);
    }
    return;
  }

  if(!client.room) return;
  const room=rooms.get(client.room);
  if(!room) return;

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
  }else if(msg.type === 'state'){
    client.snapshot=sanitizeSnapshot(client,room,msg.snapshot);
    broadcast(room.code,{type:'peer_state',clientId:client.id,snapshot:client.snapshot},client);
  }else if(msg.type === 'projectile'){
    const options=sanitizeProjectileOptions(room,client,msg.options);
    broadcast(room.code,{
      type:'projectile',
      ownerId:client.id,
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
    const amount=clamp(finiteNumber(msg.amount,0),0,1000);
    if(amount<=0) return;
    sendDamageToClient(target,{
      type:'hit',
      targetId:target.id,
      amount,
      sourceId:client.id,
      sourceName:client.name
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
    broadcast(room.code,{type:'chat',name:client.name,msg:body});
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
    ready:false, inMatch:false, serverTeam:'neutral', spawnProtectedUntil:0,
    lastSeen:Date.now(), lastParseErrorAt:0,
    chatTimes:[], chatMutedUntil:0, lastChatBody:'', lastChatAt:0,
    lastDeathDropAt:0
  };
  clients.add(client);
  socket.on('data', chunk => decodeFrames(client, chunk));
  socket.on('close', () => { removeFromRoom(client); clients.delete(client); });
  socket.on('error', () => { removeFromRoom(client); clients.delete(client); });
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
    if(room.clients.size===0){rooms.delete(code);continue;}
    tickRoomSafely(code,room,50);
  }
},50);
setInterval(()=>{
  const now=Date.now();
  for(const [code,room] of rooms){
    if(room.clients.size===0){rooms.delete(code);continue;}
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
  console.log(`Fragment.io multiplayer server running on port ${PORT}`);
  console.log("Leader chooses the mode. Everyone in the room must press READY before the match starts.");
});