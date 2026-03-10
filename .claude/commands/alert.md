Send a Telegram alert summarizing what was done in this babysit cycle.

Steps:

1. Get the latest commit hash and message:
   ```
   git log -1 --format="%H %s"
   ```

2. Build the GitHub diff URL: `https://github.com/Vilin97/aristotle/commit/<full-hash>`

3. Compose a 1-2 sentence summary of what was done (e.g. "Closed 1 sorry, submitted 2 lemmas to Aristotle").

4. Send a Telegram message via curl (token from env):
   ```
   source .env && curl -s -X POST "https://api.telegram.org/bot${TELEGRAM_BOT_TOKEN}/sendMessage" \
     -d chat_id=398863010 \
     -d parse_mode=Markdown \
     --data-urlencode "text=<summary>. [Diff](<github-url>)"
   ```
