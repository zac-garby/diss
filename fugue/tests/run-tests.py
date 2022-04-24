from subprocess import Popen, PIPE
import re

with open("eval.fugue.tests", "r") as f:
    lines = f.read().split("\n")
    cases = []

    i = 0
    while i + 1 < len(lines):
        cases.append((lines[i], lines[i + 1]))
        i += 3

ansi_escape = re.compile("(\\x1b\\[0;(\\d)*m)|(\\x1b\\[0m)")
find_answer = re.compile("= (.+)")
        
def run_case(i, c):
    print(" %4d: " % i, end="")
    
    expr, expected = c
    with Popen(["fugue"],
               stdin=PIPE,
               stdout=PIPE,
               stderr=PIPE) as proc:
        
        proc.stdin.write(":l ../prelude\n".encode("utf-8"))
        proc.stdin.write(expr.encode("utf-8"))
        proc.stdin.close()
        
        out = proc.stdout.read().decode("utf-8")
        out = ansi_escape.sub("", out)
        actual = find_answer.findall(out)

        if len(actual) < 1:
            print("FAIL:", expr, "got no result")
        elif expected == actual[0]:
            print("pass:", expr)
        else:
            print("FAIL:", expr, "expected", expected, "but got", actual[0])
        
for i, c in enumerate(cases):
    run_case(i, c)
