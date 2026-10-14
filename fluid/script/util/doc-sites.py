import re, sys, os
root = sys.argv[1]
paths = [os.path.join(root, "fluid"), os.path.join(root, "test/fluid")]
def find(mod):
    for p in paths:
        f = os.path.join(p, mod + ".fld")
        if os.path.exists(f): return f
    raise SystemExit("not found: " + mod)
def code(line):
    return line.split("#", 1)[0]
def sites(f):
    return sum(len(re.findall(r"@doc\b", code(l))) for l in open(f))
def imports(f):
    return [m.group(1).replace(".", "/") for l in open(f) if (m := re.match(r"\s*import\s+([\w.]+)", l))]
fixtures = ["conv","edge_detect","emboss","gaussian","dtw","line_chart","grouped_bar_chart","stacked_bar_chart","bar_chart_line_chart","stacked_bar_scatter_plot"]
print("Test-Name,Doc-Sites,Doc-Sites-Own,Modules-With-Doc")
for fx in fixtures:
    start = find("slicing/intermediates/" + fx)
    seen, todo = [], ["lib/prelude", "slicing/intermediates/" + fx]
    while todo:
        m = todo.pop()
        if m in seen: continue
        seen.append(m); todo += imports(find(m))
    per = {m: sites(find(m)) for m in seen}
    withdoc = ";".join(f"{m}={n}" for m, n in per.items() if n)
    print(f"slicing/intermediates/{fx}.fld,{sum(per.values())},{per['slicing/intermediates/'+fx]},{withdoc}")
