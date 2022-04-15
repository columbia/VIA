#!/usr/bin/python3

import sys
from decimal import Decimal

f = open(sys.argv[1])
lines = f.readlines()
f.close()
s = 0
i = 0
for line in lines:
    try:
    	s += Decimal(line)
    except:
        continue
    i += 1
print(s / i)
