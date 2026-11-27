"""Announce package version in Slack with release notes; with --print, print announcement instead"""

import json
import os
import pathlib
import re
import subprocess
import sys
import urllib.request

SCRIPTS = pathlib.Path(__file__).resolve().parent
PACKAGE = json.loads((SCRIPTS.parent / "package.json").read_text())


def markdown_to_slack(line: str) -> str:
    line = line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    line = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r"<\2|\1>", line)
    return re.sub(r"^- ", "• ", re.sub(r"^#+ (.*)$", r"*\1*", line))


name, version = PACKAGE["name"], PACKAGE["version"]
notes = subprocess.run([sys.executable, SCRIPTS / "release-notes.py"],
                       check=True, stdout=subprocess.PIPE, text=True).stdout
text = "\n".join([f"<https://www.npmjs.com/package/{name}/v/{version}|{name} {version}> published", ""]
                 + [markdown_to_slack(line) for line in notes.splitlines()[2:]]).strip()
if sys.argv[1:] == ["--print"]:
    print(text)
else:
    urllib.request.urlopen(urllib.request.Request(
        os.environ["SLACK_WEBHOOK_URL"],
        json.dumps({"text": text, "unfurl_links": False}).encode(),
        {"Content-Type": "application/json"}))
