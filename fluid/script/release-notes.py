"""Print milestone release notes up to package version as Markdown; with --latest, latest release alone"""

import json
import pathlib
import subprocess
import sys

PACKAGE = json.loads((pathlib.Path(__file__).resolve().parents[1] / "package.json").read_text())
KINDS = ["Features", "Bug fixes", "Other"]


def output(*command):
    return subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True).stdout


def github(query):
    """Query repository; return results from every page"""
    pages = json.loads(output("gh", "api", "--paginate", "--slurp", "repos/{owner}/{repo}/" + query))
    return [result for page in pages for result in page]


def release(version):
    """Strip pre-release suffix from version"""
    return version.split("-")[0]


def kind(issue):
    issue_type = (issue.get("type") or {}).get("name")
    if issue_type == "Problem":
        return "Bug fixes"
    implementation = "implementation" in [label["name"] for label in issue["labels"]]
    return "Features" if issue_type == "Content" and implementation else "Other"


def render(issues):
    """Line per issue, under heading for each kind of issue present"""
    lines = []
    for k in KINDS:
        titles = [f"- {issue['title']} ([#{issue['number']}]({issue['html_url']}))" for issue in issues
                  if kind(issue) == k]
        if titles:
            lines += ["", f"### {k}"] + titles
    return lines


version = PACKAGE["version"]
minor = ".".join(version.split(".")[:2])
milestone = f"{PACKAGE['name'].split('/')[-1]} {minor}"
[number] = [m["number"] for m in github("milestones?state=all&per_page=100") if m["title"] == milestone]
# Time each release was published, to the second, as issues record time of closing
times = json.loads(output("npm", "view", "--workspaces=false", PACKAGE["name"], "time", "--json"))
published = {v: time[:19] for v, time in times.items() if v.startswith(minor + ".") and v == release(v)}

# Time of last merge into milestone branch from branches named after each issue
merged = {}
for pull in github(f"pulls?state=closed&base={milestone.replace(' ', '-')}&per_page=100"):
    if pull["merged_at"]:
        issue_number = pull["head"]["ref"].split("-")[0]
        merged[issue_number] = max(merged.get(issue_number, ""), pull["merged_at"])


def completed(issue):
    """Time of last merge from issue branch, else time issue closed"""
    return merged.get(str(issue["number"]), issue["closed_at"])[:19]


def heading(issue):
    """First release published after issue completed, else release of package version"""
    return next((v for v in sorted(published, key=published.get) if published[v] > completed(issue)),
                release(version))


# Completed issues without sub-issues; most recently completed first
issues = sorted((issue for issue in github(f"issues?milestone={number}&state=closed&per_page=100")
                 if "pull_request" not in issue and issue["state_reason"] == "completed"
                 and not issue["sub_issues_summary"]["total"]),
                key=completed, reverse=True)

if sys.argv[1:] == ["--latest"]:
    lines = render([issue for issue in issues if heading(issue) == release(version)])[1:]
else:
    lines = [f"# {milestone}"]
    for h in dict.fromkeys(map(heading, issues)):
        lines += ["", f"## {h}"] + render([issue for issue in issues if heading(issue) == h])
print("\n".join(lines))
