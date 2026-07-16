Fragment.io Multiplayer Build - Online Sync Pass 2

Run locally:
  node server.js

Open:
  http://localhost:3000

Online/Cloudflare Tunnel:
  cloudflared tunnel --url http://localhost:3000

What this build syncs online:
- Lobby leader + ready system
- Mode choice by leader only
- Player snapshots, cosmetics, sidegrades/Core Matrix labels, shots, hit relay, chat
- Server-authoritative bots with lower counts and improved AI
- Server-authoritative bot and boss damage
- Server-authoritative fragments and pickups
- Server-authoritative world changes, world zones, terrain formations, and hot zones
- Server-authoritative boss spawns, boss HP, boss movement, boss shots, boss rewards
- Remote player death events/custom final-evolution death animations
- PvP No Bots mode keeps bots disabled but still uses shared fragments/terrain/hot-zone state where applicable

Notes:
- Keep node server.js open while playing.
- For international friends, keep the cloudflared terminal open too.
- If testing with two tabs, both tabs should see identical bot IDs, fragments, terrain, hot zones, bosses, and player sidegrade names.
