"""Print release notes as Markdown for milestone of package version"""

import json
import pathlib
import subprocess
from typing import Any

PACKAGE = json.loads((pathlib.Path(__file__).resolve().parents[1] / "package.json").read_text())
KINDS = ["Features", "Bug fixes", "Other"]


def github(path: str) -> list[dict[str, Any]]:
    command = ["gh", "api", "--paginate", "--slurp", "repos/{owner}/{repo}/" + path]
    pages = json.loads(subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True).stdout)
    return [result for page in pages for result in page]


def kind(issue: dict[str, Any]) -> str:
    issue_type = (issue.get("type") or {}).get("name")
    if issue_type == "Problem":
        return "Bug fixes"
    implementation = "implementation" in [label["name"] for label in issue["labels"]]
    return "Features" if issue_type == "Content" and implementation else "Other"


milestone = f"{PACKAGE['name'].split('/')[-1]} {'.'.join(PACKAGE['version'].split('.')[:2])}"
[number] = [m["number"] for m in github("milestones?state=all&per_page=100") if m["title"] == milestone]
issues = sorted((issue for issue in github(f"issues?milestone={number}&state=closed&per_page=100")
                 if "pull_request" not in issue and issue["state_reason"] == "completed"
                 and not issue["sub_issues_summary"]["total"]),
                key=lambda issue: issue["closed_at"])
lines = [f"# {milestone}"]
for k in KINDS:
    titles = [f"- {issue['title']} ([#{issue['number']}]({issue['html_url']}))" for issue in issues
              if kind(issue) == k]
    if titles:
        lines += ["", f"## {k}"] + titles
print("\n".join(lines))
