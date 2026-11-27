"""Announce package version in Slack with release notes; without SLACK_WEBHOOK_URL, print announcement"""

import json
import os
import pathlib
import re
import subprocess
import sys
import urllib.request

SCRIPTS = pathlib.Path(__file__).resolve().parent
PACKAGE = json.loads((SCRIPTS.parent / "package.json").read_text())


def mrkdwn(line):
    """Convert line of Markdown to Slack markup"""
    line = line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    line = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r"<\2|\1>", line)
    return re.sub(r"^- ", "• ", re.sub(r"^#+ (.*)$", r"*\1*", line))


name, version = PACKAGE["name"], PACKAGE["version"]
notes = subprocess.run([sys.executable, SCRIPTS / "release-notes.py"],
                       check=True, stdout=subprocess.PIPE, text=True).stdout
text = "\n".join([f"<https://www.npmjs.com/package/{name}/v/{version}|{name} {version}> published", ""]
                 + [mrkdwn(line) for line in notes.splitlines()[2:]]).strip()
webhook = os.environ.get("SLACK_WEBHOOK_URL")
if webhook:
    urllib.request.urlopen(urllib.request.Request(
        webhook,
        json.dumps({"text": text, "unfurl_links": False}).encode(),
        {"Content-Type": "application/json"}))
else:
    print(text)
