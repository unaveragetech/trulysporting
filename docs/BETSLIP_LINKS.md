# Opening a parlay at a sportsbook

**Goal:** one click from a parlay on the Parlays page to the sportsbook, with the legs already on the slip.

## What the research found

No sportsbook documents a public "add these N legs" link, so what is possible differs by book:

| Book | What we do | Basis |
|---|---|---|
| DraftKings | One link with every leg: `https://sportsbook.draftkings.com/?outcomes=ID1+ID2+...` | Unofficial. One developer's notes say the site reads several ids from `outcomes` joined by `+` ([DEMON-X13/nfl-hub#223](https://github.com/DEMON-X13/nfl-hub/pull/223), [#278](https://github.com/DEMON-X13/nfl-hub/pull/278)). The ids are DraftKings' own, taken from the betslip links ESPN embeds for its DraftKings lines, so they are the exact markets we priced. |
| FanDuel and other books | One link per leg, using Unabated's own `deepLink` (partner-tagged, path untouched) | FanDuel's `addToBetslip?marketId=..&selectionId=..` form is single-selection ([The Odds API](https://the-odds-api.com/releases/deep-links.html)); Unabated's rules say not to edit or merge their links, so we do not build a combined FanDuel link. |
| Kalshi / Novig / Polymarket | Shown as single-bet routes only | They do not sell parlays. |
| Player props | Listed to add by hand | No price feed, so no id or link. |

Link behaviour is each book's own ([SharpAPI notes](https://docs.sharpapi.io/api-reference/deeplinks): whether a link preselects a bet depends on what the book's site accepts). **The DraftKings multi-leg link could not be tested by us (the book is not reachable from our test browser), so the page tells users to check every leg is on the slip.**

## Safety checks before any link is shown

The parlay is re-priced live and passes `parlay_venues.evaluate`: every leg quoted at the exact saved line, fresh and sane prices, no game started or about to start, no leg priced shorter than about -2500. If nothing passes, no link is offered. The page never places a bet.
