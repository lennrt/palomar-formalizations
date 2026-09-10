#!/usr/bin/env python3
"""Adapt Comparator's argument boundary to the pinned Landrun CLI.

Strict allowlist; never allow flags that turn off a sandbox restriction.
This small independent implementation follows the documented CLI behavior.
"""
import os,sys
binary=os.environ.get('PALOMAR_LANDRUN_BIN')
if not binary:raise SystemExit('PALOMAR_LANDRUN_BIN is required')
flags={'--best-effort','-ldd','--ldd','-add-exec','--add-exec','--ignore-missing',
       '--log-disable-originating','--log-enable-subprocesses','--log-disable-subdomains'}
values={'--log-level','--ro','--rox','--rw','--rwx','--unix','--bind-tcp','--connect-tcp','--env'}
a=sys.argv[1:];opts=[]
while a and a[0].startswith('-'):
 x=a.pop(0)
 if x in flags:opts.append(x)
 elif x in values:
  if not a:raise SystemExit('Missing value for '+x)
  opts.extend([x,a.pop(0)])
 else:raise SystemExit('Refusing unknown or restriction-disabling flag '+x)
if not a:raise SystemExit('Comparator supplied no sandboxed command')
os.execv(binary,[binary,*opts,'--',*a])
