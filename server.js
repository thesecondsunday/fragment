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
const rooms = new Map();
const clients = new Set();

function id(bytes = 8){ return crypto.randomBytes(bytes).toString('hex'); }
function cleanRoom(v){ return String(v || '').trim().toUpperCase().replace(/[^A-Z0-9-]/g, '').slice(0,18) || crypto.randomBytes(3).toString('hex').toUpperCase(); }
function safeName(v){ return String(v || 'Player').replace(/[<>]/g,'').slice(0,24) || 'Player'; }
function cleanMode(v){
  const mode = String(v || 'normal').toLowerCase();
  return ['normal','test','duo','teams','br','bossrush','pvp'].includes(mode) ? mode : 'normal';
}
function clamp(v, a, b){ return Math.max(a, Math.min(b, v)); }
function rand(a, b){ return a + Math.random() * (b - a); }
function irand(a, b){ return Math.floor(rand(a, b)); }
function dist(a, b){ return Math.hypot((a.x||0)-(b.x||0), (a.y||0)-(b.y||0)); }
function angleDiff(a, b){ return Math.atan2(Math.sin(a-b), Math.cos(a-b)); }

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
  return {
    type:'lobby_state',
    room:room.code,
    leaderId:room.leaderId,
    mode:room.mode,
    matchStarted:room.matchStarted,
    players:[...room.clients].map(c=>({clientId:c.id, name:c.name, ready:!!c.ready, leader:c.id===room.leaderId, inMatch:!!c.inMatch}))
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
  if(!client || client.socket.destroyed) return false;
  try{
    const data = Buffer.from(JSON.stringify(obj));
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
  }catch(e){ return false; }
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
  // Lower, readable online counts. Large local bot swarms looked cluttered online and made synced combat hard to read.
  if(mode === 'pvp' || mode === 'bossrush') return 0;
  if(mode === 'test') return 6;
  if(mode === 'duo') return 8;
  if(mode === 'teams') return 12;
  if(mode === 'br') return 16;
  return 6;
}
function teamForBot(mode, i){
  if(mode === 'teams') return i < 24 ? 'blue' : 'red';
  if(mode === 'duo') return 'red';
  if(mode === 'test') return 'red';
  return 'neutral';
}
function spawnServerBots(room){
  room.bots = [];
  const count = botCountForMode(room.mode);
  for(let i=0;i<count;i++){
    const team = teamForBot(room.mode, i);
    const passive = room.mode === 'test';
    const namePrefix = room.mode === 'br' ? 'BR ' : room.mode === 'teams' ? (team === 'blue' ? 'Blue ' : 'Red ') : '';
    const bot = {
      id:'bot_' + id(5),
      name: passive ? `Dummy ${String(i+1).padStart(2,'0')}` : `${namePrefix}${botNames[i % botNames.length]}-${String(i+1).padStart(2,'0')}`,
      x: room.mode === 'test' ? ((i % 4) - 1.5) * 260 : rand(-HALF_W+360, HALF_W-360),
      y: room.mode === 'test' ? (Math.floor(i / 4) - 1) * 230 : rand(-HALF_H+360, HALF_H-360),
      vx:0, vy:0, r:18, angle:rand(0, Math.PI*2),
      hp: passive ? 280 : 115, maxHp: passive ? 280 : 115,
      score:0, frags:0, level:1,
      team, ally:team === 'blue', passive,
      archetype: archetypes[i % archetypes.length],
      bodyColor: passive ? '#7fd8ff' : colors[i % colors.length],
      fireCd: rand(0.35, 1.2), think:0, strafe:Math.random()<0.5 ? -1 : 1,
      aimError:rand(-0.10,0.10), dodge:rand(.75,1.25), confidence:rand(.75,1.22),
      meleeCd:0, lastTargetId:null,
      roamX:rand(-HALF_W+260, HALF_W-260), roamY:rand(-HALF_H+260, HALF_H-260),
      dead:false, respawnAt:0, lastHitBy:null
    };
    room.bots.push(bot);
  }
}
function startMatch(room){
  room.matchStarted = true;
  room.matchId++;
  for(const c of room.clients){ c.inMatch = true; }
  spawnServerBots(room);
  initSharedWorld(room);
  const botsState = {type:'bots_state', mode:room.mode, bots:room.bots.map(botSnapshot), immediate:true};
  broadcast(room.code, {type:'match_start', mode:room.mode, matchId:room.matchId, startedAt:Date.now()});
  broadcast(room.code, botsState);
  broadcastSharedState(room, true);
  broadcastLobby(room);
}
function maybeStartMatch(room){
  if(room.matchStarted) return;
  // Online matches intentionally require at least two connected players.
  // This prevents the leader from accidentally launching before friends join.
  if(room.clients.size < 2) return;
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
function botCanTarget(bot, snap){
  if(!snap || snap.dead) return false;
  if(bot.team && snap.team && bot.team !== 'neutral' && snap.team !== 'neutral' && bot.team === snap.team) return false;
  return true;
}
function nearestTargetForBot(room, bot){
  let best=null, bestD=Infinity;
  for(const snap of livePlayerSnapshots(room)){
    if(!botCanTarget(bot, snap)) continue;
    const d = Math.hypot((snap.x||0)-bot.x, (snap.y||0)-bot.y);
    if(d < bestD){ bestD = d; best = snap; }
  }
  return best ? {snap:best, d:bestD} : null;
}
function updateServerBots(room, dt){
  if(!room.matchStarted || !room.bots.length) return;
  const now = Date.now();
  for(const bot of room.bots){
    if(bot.dead){
      if(room.mode !== 'br' && now >= bot.respawnAt){
        bot.dead=false; bot.hp=bot.maxHp; bot.x=rand(-HALF_W+360, HALF_W-360); bot.y=rand(-HALF_H+360, HALF_H-360);
        bot.vx=0; bot.vy=0; bot.fireCd=rand(.4,1.1); bot.score=0; bot.frags=0; bot.lastHitBy=null; bot.meleeCd=0; bot.aimError=rand(-0.10,0.10);
      }
      continue;
    }
    if(bot.passive){ bot.angle += dt * 0.0009; continue; }
    bot.think -= dt/1000;
    if(bot.think <= 0){
      bot.think = rand(.35,.9);
      if(Math.random()<.4) bot.strafe *= -1;
      if(Math.random()<.25){ bot.roamX=rand(-HALF_W+260, HALF_W-260); bot.roamY=rand(-HALF_H+260, HALF_H-260); }
    }
    const target = nearestTargetForBot(room, bot);
    let moveX=0, moveY=0;
    if(target && target.d < 1180){
      const snap = target.snap;
      bot.lastTargetId = snap.id || target.client?.id || null;
      const px = (snap.x||0) + (snap.vx||0) * 8;
      const py = (snap.y||0) + (snap.vy||0) * 8;
      const targetAngle = Math.atan2(py-bot.y, px-bot.x);
      bot.angle = targetAngle;
      const towardX=Math.cos(bot.angle), towardY=Math.sin(bot.angle);
      const sideX=-Math.sin(bot.angle)*bot.strafe, sideY=Math.cos(bot.angle)*bot.strafe;
      const desired = ['ronin','swordsman','world_eater','bloodlord'].includes(bot.archetype) ? 86 : ['deadeye','solar_lance','sniper'].includes(bot.archetype) ? 430 : 250;
      const lowHp = bot.hp < bot.maxHp * .34;
      if(lowHp && target.d < 360){ moveX -= towardX*1.05; moveY -= towardY*1.05; moveX += sideX*.65; moveY += sideY*.65; }
      else if(target.d > desired+70){ moveX += towardX*.92 + sideX*.22; moveY += towardY*.92 + sideY*.22; }
      else if(target.d < desired-50){ moveX -= towardX*.82; moveY -= towardY*.82; moveX += sideX*.50; moveY += sideY*.50; }
      else { moveX += sideX*(1.05*bot.dodge); moveY += sideY*(1.05*bot.dodge); }

      bot.meleeCd = Math.max(0, (bot.meleeCd||0)-dt/1000);
      if(['ronin','swordsman','world_eater','bloodlord'].includes(bot.archetype) && target.d < 118 && bot.meleeCd<=0){
        bot.meleeCd = rand(.46,.78);
        const amount = bot.archetype==='ronin' ? 13 : 10;
        send(snap.client, {type:'bot_hit', botId:bot.id, botName:bot.name, amount, cause:'melee'});
      }

      bot.fireCd -= dt/1000;
      if(bot.fireCd <= 0 && target.d < 780){
        const rapid = ['bullet_storm','machine','minigunner'].includes(bot.archetype);
        const long = ['deadeye','solar_lance','sniper'].includes(bot.archetype);
        bot.fireCd = rapid ? rand(.20,.38) : long ? rand(.52,.88) : rand(.38,.72);
        bot.aimError = bot.aimError*0.45 + rand(-0.15,0.15)*0.55;
        const spread = (long ? rand(-0.07,0.07) : rand(-0.13,0.13)) + bot.aimError;
        const angle = targetAngle + spread;
        const shot = {kind:'basic', speed:long?9.4:8.2, life:long?120:105, dmg:long?14:rapid?6.2:8.5, color:bot.bodyColor, size:rapid?4:5, visualOnly:true, networkReplay:true};
        broadcast(room.code, {type:'bot_projectile', botId:bot.id, bot:botSnapshot(bot), angle, options:shot, serial:++room.lastShotSerial});
        const trueAngle = Math.atan2((snap.y||0)-bot.y, (snap.x||0)-bot.x);
        const aim = Math.abs(angleDiff(angle, trueAngle));
        const rangeFactor = clamp(1 - target.d / 920, .18, .92);
        const accuracy = clamp((long?.56:.48) + rangeFactor*.34 - aim*1.05, .18, .88) * bot.confidence;
        if(aim < .34 && Math.random() < accuracy){
          send(snap.client, {type:'bot_hit', botId:bot.id, botName:bot.name, amount:shot.dmg, cause:'projectile'});
        }
      }
    }else{
      const dx=bot.roamX-bot.x, dy=bot.roamY-bot.y, L=Math.hypot(dx,dy)||1;
      if(L<70){ bot.roamX=rand(-HALF_W+260, HALF_W-260); bot.roamY=rand(-HALF_H+260, HALF_H-260); }
      moveX += dx/L*.65; moveY += dy/L*.65; bot.angle=Math.atan2(dy,dx);
    }
    for(const other of room.bots){
      if(other===bot || other.dead) continue;
      const d=Math.hypot(bot.x-other.x, bot.y-other.y);
      if(d>0 && d<145){ moveX += (bot.x-other.x)/d * ((145-d)/145)*1.4; moveY += (bot.y-other.y)/d * ((145-d)/145)*1.4; }
    }
    if(bot.x < -HALF_W+260) moveX += 1;
    if(bot.x > HALF_W-260) moveX -= 1;
    if(bot.y < -HALF_H+260) moveY += 1;
    if(bot.y > HALF_H-260) moveY -= 1;
    const mag = Math.hypot(moveX, moveY) || 1;
    const sp = ['ronin','swordsman'].includes(bot.archetype) ? 4.2 : 3.35;
    bot.vx = bot.vx*0.86 + (moveX/mag)*sp*0.14;
    bot.vy = bot.vy*0.86 + (moveY/mag)*sp*0.14;
    bot.x = clamp(bot.x + bot.vx * dt/16.6, -HALF_W+20, HALF_W-20);
    bot.y = clamp(bot.y + bot.vy * dt/16.6, -HALF_H+20, HALF_H-20);
  }
  if(now - room.lastBotBroadcast > 100){
    room.lastBotBroadcast = now;
    broadcast(room.code, {type:'bots_state', mode:room.mode, bots:room.bots.map(botSnapshot)});
  }
}



// -----------------------------
// Shared terrain + hot-zone state
// -----------------------------
const sharedBiomes = [
  {name:'Meadow', x:-HALF_W, y:-HALF_H, w:WORLD_W/4, h:WORLD_H/2, color:'#2f5d45', detail:'#3d7455', accent:'#92d96d'},
  {name:'Frozen Wastes', x:-HALF_W+WORLD_W/4, y:-HALF_H, w:WORLD_W/4, h:WORLD_H/2, color:'#5d87a5', detail:'#709ab7', accent:'#d8f3ff'},
  {name:'Volcanic Basin', x:-HALF_W+WORLD_W/2, y:-HALF_H, w:WORLD_W/4, h:WORLD_H/2, color:'#7c4a3c', detail:'#9d6152', accent:'#ff8a54'},
  {name:'Sky Salt Flats', x:-HALF_W+WORLD_W*3/4, y:-HALF_H, w:WORLD_W/4, h:WORLD_H/2, color:'#718391', detail:'#8b9aa5', accent:'#f3fbff'},
  {name:'Ancient Forest', x:-HALF_W, y:0, w:WORLD_W/4, h:WORLD_H/2, color:'#345f3f', detail:'#46734d', accent:'#80c75a'},
  {name:'Crystal Desert', x:-HALF_W+WORLD_W/4, y:0, w:WORLD_W/4, h:WORLD_H/2, color:'#b2a37d', detail:'#c7b994', accent:'#fff0a6'},
  {name:'Corrupted Void', x:-HALF_W+WORLD_W/2, y:0, w:WORLD_W/4, h:WORLD_H/2, color:'#5b4267', detail:'#765689', accent:'#cb80ff'},
  {name:'Storm Coast', x:-HALF_W+WORLD_W*3/4, y:0, w:WORLD_W/4, h:WORLD_H/2, color:'#42566d', detail:'#526a83', accent:'#b9d4ff'}
];
const terrainTypes = ['crater','vine','ice','void','road'];
function spawnSharedTerrainFeature(room, type=null, x=null, y=null){
  type = type || terrainTypes[irand(0, terrainTypes.length)];
  x = x ?? rand(-HALF_W+380, HALF_W-380);
  y = y ?? rand(-HALF_H+320, HALF_H-320);
  const feature = {id:'terrain_'+(++room.lastTerrainSerial)+'_'+id(3), type, x, y, life:rand(44,78), spawn:1.35, r:type==='road'?170:type==='vine'?120:type==='crater'?95:type==='void'?115:135, angle:rand(0,Math.PI)};
  room.terrainFeatures.push(feature);
  if(room.terrainFeatures.length>28) room.terrainFeatures.splice(0, room.terrainFeatures.length-28);
  broadcast(room.code, {type:'terrain_event', action:'spawn', feature:terrainSnapshot(feature)});
  return feature;
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
function fragCountsForMode(mode){
  if(mode === 'bossrush') return {xp:0,natural:0,ability:0,evo:0,world:0,cursed:0};
  if(mode === 'test') return {xp:26,natural:8,ability:5,evo:3,world:0,cursed:0};
  if(mode === 'pvp') return {xp:60,natural:24,ability:8,evo:5,world:1,cursed:2};
  return {xp:78,natural:30,ability:8,evo:5,world:1,cursed:2};
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
function initSharedFragments(room){
  room.fragments = [];
  const counts = fragCountsForMode(room.mode);
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
  if(!room.matchStarted || room.mode === 'bossrush') return;
  const counts = {xp:0,natural:0,ability:0,evo:0,world:0,cursed:0};
  for(const f of room.fragments) counts[f.kind] = (counts[f.kind]||0)+1;
  const want = fragCountsForMode(room.mode);
  if(counts.xp < want.xp) spawnSharedFragment(room,'xp');
  if(counts.natural < want.natural && Math.random()<.65) spawnSharedFragment(room,'natural');
  if(counts.ability < want.ability && Math.random()<.30) spawnSharedFragment(room,'ability');
  if(counts.evo < want.evo && Math.random()<.18) spawnSharedFragment(room,'evo');
  if(counts.world < want.world && !room.world.mode && Math.random()<.08) spawnSharedFragment(room,'world');
  if(counts.cursed < want.cursed && Math.random()<.07) spawnSharedFragment(room,'cursed');
  if(room.fragments.length > 190) room.fragments.splice(0, room.fragments.length-190);
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
    const d=Math.hypot((snap.x||0)-boss.x,(snap.y||0)-boss.y);
    if(d<bestD){bestD=d; best=snap;}
  }
  return best ? {snap:best,d:bestD} : null;
}
function updateSharedBosses(room, dt){
  if(!room.matchStarted || ['pvp','test','br','bossrush'].includes(room.mode)) return;
  const now=Date.now();
  if(now > room.nextBossAt){ spawnSharedBoss(room); room.nextBossAt = now + rand(70000,100000); }
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
      if(d>desired+80){ mx=tx; my=ty; } else if(d<desired-120){ mx=-tx; my=-ty; } else { mx=-Math.sin(b.angle)*0.75; my=Math.cos(b.angle)*0.75; }
      b.vx=b.vx*0.90 + mx*b.speed*0.10;
      b.vy=b.vy*0.90 + my*b.speed*0.10;
      b.fireCd -= dt/1000;
      if(b.fireCd<=0 && d<760){
        b.fireCd = rand(.72,1.35);
        const shot={kind:'boss', speed:5.2, life:135, dmg:13, color:b.color, size:9, visualOnly:true, networkReplay:true};
        broadcast(room.code, {type:'boss_projectile', bossId:b.id, boss:bossSnapshot(b), angle:b.angle+rand(-.16,.16), options:shot});
        if(d<650 && Math.random()<.42) send(snap.client, {type:'boss_hit', bossId:b.id, bossName:b.name, amount:shot.dmg});
      }
    }else{ b.vx*=0.92; b.vy*=0.92; }
    b.x=clamp(b.x+b.vx*dt/16.6, -HALF_W+80, HALF_W-80);
    b.y=clamp(b.y+b.vy*dt/16.6, -HALF_H+80, HALF_H-80);
  }
  room.bosses = room.bosses.filter(b=>!b.removeAt || Date.now()<b.removeAt);
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
  if(now-room.lastFragmentBroadcast>550){ room.lastFragmentBroadcast=now; broadcast(room.code, {type:'fragments_state', fragments:room.fragments.map(fragmentSnapshot)}); }
  if(now-room.lastWorldBroadcast>450){ room.lastWorldBroadcast=now; broadcast(room.code, {type:'world_state', world:worldSnapshot(room)}); }
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

function handleMessage(client, msg){
  if(typeof msg !== 'object' || !msg) return;
  if(msg.type === 'join'){
    removeFromRoom(client);
    const room = getRoom(msg.room);
    client.room = room.code;
    client.name = safeName(msg.name);
    client.mode = cleanMode(msg.mode);
    client.ready = false;
    client.inMatch = false;
    if(room.clients.size === 0){ room.mode = client.mode; room.matchStarted = false; room.bots = []; room.fragments = []; room.bosses = []; room.terrainFeatures=[]; room.hotZone=null; room.nextTerrainAt=Date.now()+9000; room.nextHotZoneAt=Date.now()+16000; room.world = {mode:null,timer:0,zones:[],nextAt:Date.now()+22000}; room.nextBossAt=Date.now()+32000; }
    room.clients.add(client);
    chooseLeader(room);
    send(client, {type:'welcome', clientId:client.id, room:room.code});
    const peers = peersFor(client);
    if(peers.length) send(client, {type:'peers', peers});
    broadcast(room.code, {type:'peer_joined', clientId:client.id, name:client.name, mode:room.mode}, client);
    broadcastLobby(room);
    if(room.matchStarted){
      client.inMatch = true;
      send(client, {type:'match_start', mode:room.mode, matchId:room.matchId, startedAt:Date.now(), lateJoin:true});
      send(client, {type:'bots_state', mode:room.mode, bots:room.bots.map(botSnapshot)});
      sendSharedState(client, room, true);
    }
    return;
  }
  if(!client.room) return;
  const room = rooms.get(client.room);
  if(!room) return;
  if(msg.type === 'mode_change'){
    if(client.id !== room.leaderId || room.matchStarted) return;
    room.mode = cleanMode(msg.mode);
    for(const c of room.clients) c.ready = false;
    broadcastLobby(room);
  }else if(msg.type === 'ready'){
    if(room.matchStarted) return;
    client.ready = !!msg.ready;
    if(msg.mode && client.id === room.leaderId) room.mode = cleanMode(msg.mode);
    broadcastLobby(room);
    maybeStartMatch(room);
  }else if(msg.type === 'state'){
    client.snapshot = msg.snapshot || null;
    if(client.snapshot){
      client.snapshot.id = client.id;
      client.snapshot.name = safeName(client.snapshot.name || client.name);
      client.snapshot.team = client.snapshot.team || (room.mode === 'teams' ? (client.id === room.leaderId ? 'blue' : 'red') : 'neutral');
    }
    broadcast(room.code, {type:'peer_state', clientId:client.id, snapshot:client.snapshot}, client);
  }else if(msg.type === 'projectile'){
    broadcast(room.code, {type:'projectile', ownerId:client.id, angle:Number(msg.angle)||0, options:msg.options || {}}, client);
  }else if(msg.type === 'hit'){
    broadcast(room.code, {type:'hit', targetId:String(msg.targetId||''), amount:Number(msg.amount)||0, sourceId:client.id, sourceName:client.name}, client);
  }else if(msg.type === 'fragment_collect'){
    collectSharedFragment(room, client, String(msg.id||''));
  }else if(msg.type === 'boss_hit'){
    const boss = room.bosses.find(b=>b.id === String(msg.bossId||''));
    if(!boss || boss.dead) return;
    const amount = clamp(Number(msg.amount)||0, 0, 450);
    boss.hp -= amount;
    if(boss.hp <= 0){
      boss.hp = 0; boss.dead = true; boss.removeAt = Date.now()+650;
      for(let i=0;i<34;i++) spawnSharedFragment(room, i%5===0?'natural':'xp', boss.x+rand(-150,150), boss.y+rand(-150,150));
      spawnSharedFragment(room, 'ability', boss.x, boss.y, ['judgement_laser','fragment_storm','reflect_shield','loot_radar'][irand(0,4)]);
      send(client, {type:'boss_award', bossId:boss.id, bossName:boss.name, xp:520, score:2800});
      broadcast(room.code, {type:'boss_event', action:'killed', bossId:boss.id, bossName:boss.name, killerId:client.id, killerName:client.name});
    }
  }else if(msg.type === 'bot_hit'){
    const bot = room.bots.find(b=>b.id === String(msg.botId||''));
    if(!bot || bot.dead) return;
    const amount = clamp(Number(msg.amount)||0, 0, 250);
    bot.hp -= amount;
    bot.lastHitBy = client.id;
    if(bot.hp <= 0){
      bot.dead = true;
      bot.hp = 0;
      bot.respawnAt = Date.now() + (room.mode === 'br' ? 999999999 : 2500);
      bot.score = 0;
      for(let i=0;i<10;i++) spawnSharedFragment(room, 'xp', bot.x+rand(-46,46), bot.y+rand(-46,46));
      if(Math.random()<.22) spawnSharedFragment(room, 'ability', bot.x+rand(-70,70), bot.y+rand(-70,70));
      send(client, {type:'bot_award', botId:bot.id, botName:bot.name, xp:40, score:250});
      broadcast(room.code, {type:'bot_killed', botId:bot.id, botName:bot.name, killerId:client.id, killerName:client.name});
    }
  }else if(msg.type === 'player_death'){
    const snap = msg.snapshot || client.snapshot || {};
    const x = clamp(Number(snap.x)||0, -HALF_W+50, HALF_W-50);
    const y = clamp(Number(snap.y)||0, -HALF_H+50, HALF_H-50);
    const frags = clamp(Number(snap.frags)||0, 0, 80);
    const dropCount = clamp(12 + frags*1.2, 12, 42);
    for(let i=0;i<dropCount;i++) spawnSharedFragment(room, 'xp', x+rand(-42,42), y+rand(-42,42));
    broadcast(room.code, {type:'death_event', clientId:client.id, name:client.name, snapshot:snap, killer:msg.killer||null}, client);
    updateSharedBroadcasts(room);
  }else if(msg.type === 'chat'){
    broadcast(room.code, {type:'chat', name:client.name, msg:String(msg.msg||'').slice(0,120)}, client);
  }else if(msg.type === 'event'){
    broadcast(room.code, {...msg, sourceId:client.id}, client);
  }
}
function decodeFrames(client, chunk){
  client.buffer = client.buffer ? Buffer.concat([client.buffer, chunk]) : chunk;
  let offset = 0;
  while(client.buffer.length - offset >= 2){
    const b0 = client.buffer[offset];
    const opcode = b0 & 0x0f;
    const b1 = client.buffer[offset+1];
    const masked = (b1 & 0x80) !== 0;
    let len = b1 & 0x7f;
    let header = 2;
    if(len === 126){
      if(client.buffer.length - offset < 4) break;
      len = client.buffer.readUInt16BE(offset+2); header = 4;
    }else if(len === 127){
      if(client.buffer.length - offset < 10) break;
      const big = client.buffer.readBigUInt64BE(offset+2);
      if(big > BigInt(10 * 1024 * 1024)){ client.socket.destroy(); return; }
      len = Number(big); header = 10;
    }
    const maskBytes = masked ? 4 : 0;
    if(client.buffer.length - offset < header + maskBytes + len) break;
    let payload = client.buffer.subarray(offset + header + maskBytes, offset + header + maskBytes + len);
    if(masked){
      const mask = client.buffer.subarray(offset + header, offset + header + 4);
      payload = Buffer.from(payload.map((byte, i) => byte ^ mask[i % 4]));
    }
    offset += header + maskBytes + len;
    if(opcode === 0x8){ client.socket.end(); return; }
    if(opcode === 0x9){ sendPong(client); continue; }
    if(opcode !== 0x1) continue;
    try{ handleMessage(client, JSON.parse(payload.toString('utf8'))); }catch(e){}
  }
  client.buffer = client.buffer.subarray(offset);
}
function sendPong(client){ try{ client.socket.write(Buffer.from([0x8a, 0])); }catch(e){} }
function serveFile(req, res){
  const parsed = url.parse(req.url).pathname;
  let filePath = parsed === '/' ? path.join(ROOT, 'index.html') : path.join(ROOT, decodeURIComponent(parsed));
  if(!filePath.startsWith(ROOT)){ res.writeHead(403); res.end('Forbidden'); return; }
  fs.readFile(filePath, (err, data) => {
    if(err){ res.writeHead(404); res.end('Not found'); return; }
    const ext = path.extname(filePath).toLowerCase();
    const type = ext === '.html' ? 'text/html; charset=utf-8' : ext === '.js' ? 'text/javascript; charset=utf-8' : ext === '.css' ? 'text/css; charset=utf-8' : 'application/octet-stream';
    res.writeHead(200, {'Content-Type': type, 'Cache-Control':'no-store'});
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
  const client = {id:id(), socket, room:null, name:'Player', snapshot:null, buffer:null, ready:false, inMatch:false};
  clients.add(client);
  socket.on('data', chunk => decodeFrames(client, chunk));
  socket.on('close', () => { removeFromRoom(client); clients.delete(client); });
  socket.on('error', () => { removeFromRoom(client); clients.delete(client); });
});
setInterval(() => {
  for(const [code, room] of rooms){
    if(room.clients.size === 0){ rooms.delete(code); continue; }
    updateServerBots(room, 50);
    updateSharedWorld(room, 50);
    updateSharedBosses(room, 50);
    updateSharedBroadcasts(room);
  }
}, 50);
setInterval(() => {
  for(const [code, room] of rooms){ if(room.clients.size === 0) rooms.delete(code); else broadcastLobby(room); }
}, 5000);
server.listen(PORT, "0.0.0.0", () => {
  console.log(`Fragment.io multiplayer server running on port ${PORT}`);
  console.log("Leader chooses the mode. Everyone in the room must press READY before the match starts.");
});