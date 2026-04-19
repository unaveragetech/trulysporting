# TrulySporting Analytics 🏆

Real-time sports scores, trends, news, rankings & analytics — powered by ESPN's public APIs and built with Streamlit.

## Features

- 🏅 **Scoreboard** — Live & recent game scores with period-by-period breakdowns
- 📈 **Team Trends** — Win/loss streaks and scoring charts
- 🏟 **Teams** — Full roster & team info
- 📰 **News** — Latest headlines per league
- 🏆 **Rankings** — Current standings and polls
- 🌐 **Network** — Monitor ESPN API endpoint health *(admin)*
- 🔬 **Schema Explorer** — Browse the local database schema *(admin)*
- 🔍 **Raw Inspector** — Inspect raw API responses *(admin)*
- 📋 **Custom Views** — Save and share filtered scoreboard views
- 🛠 **Admin Panel** — Trigger daily data syncs, manage settings *(admin)*
- 💚 **Support** — Donation page (Cash App)

## Quick Start (Local)

```bash
pip install -r requirements.txt
streamlit run sporting.py
```

## Deploy to Streamlit Cloud

1. Fork / push this repo to your GitHub account
2. Go to [share.streamlit.io](https://share.streamlit.io) → **New app**
3. Select this repo, branch `main`, file `sporting.py`
4. Under **Settings → Secrets**, add:
   ```toml
   ADMIN_PIN = "your_secure_pin"
   ```
5. Click **Deploy**

## Configuration

Copy `.streamlit/secrets.toml.example` → `.streamlit/secrets.toml` and fill in your values for local dev. See the example file for all available options.

## Distributed Fetching (optional)

`coordinator.py` runs a local HTTP job queue. `fetch_node.py` can run on any PC on the same network to share the ESPN API fetch load.

```bash
# Machine 1 — coordinator
python coordinator.py

# Machine 2+ — fetch workers
python fetch_node.py --coordinator http://<coordinator_ip>:8765
```

## License

MIT
