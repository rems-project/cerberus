# for reading the JSON (ish) timing output 

import json
import io

def load_funs(fname):
  f = open(fname)
  contents = f.read()
  # FIXME: this next bit is a total hack
  i = contents.find('"name": "function"')
  while contents[i] != '{':
    i -= 1
  dec = json.JSONDecoder()
  funs = []
  while 1:
    try:
      (fun, j) = dec.raw_decode(contents[i:])
    except json.JSONDecodeError:
      break
    funs.append(fun)
    i += j
    while i < len(contents) and contents[i] != '{':
      i += 1
  return funs


def time(j):
  if 'time' in j:
    return j['time']
  return sum([time(j2) for j2 in j.get('contents', [])])


def walk_json_ctxt(f, j):
  q = [(j, [])]
  while q:
    (j, ctxt) = q.pop()
    assert type(j) == dict, type(j)
    if j.get('contents'):
      ctxt2 = ctxt + [(j['name'], j.get('details'))]
      q.extend([(j2, ctxt2) for j2 in j['contents']])
    if not j:
      continue
    f(j, ctxt)

def walk_json(f, j):
  q = [j]
  while q:
    j = q.pop()
    assert type(j) == dict, type(j)
    if 'contents' in j:
      q.extend(j['contents'])
    if not j:
      continue
    f(j)

def select(sel, j):
  q = [(j, [], [])]
  xs = []
  while q:
    (j, sel_ctxt, ctxt) = q.pop()
    if not j:
      continue
    nm = j['name']
    if sel(nm, j):
      sel_ctxt2 = sel_ctxt + [nm]
      if sel_ctxt:
        print('WARNING: nesting: %s -> %s' % (sel_ctxt, nm))
      xs.append((j, ctxt))
    else:
      sel_ctxt2 = sel_ctxt
    if j.get('contents', []):
      ctxt2 = ctxt + [(j['name'], j.get('details'))]
      q.extend([(j2, sel_ctxt2, ctxt2) for j2 in j.get('contents', [])])
  tot_sel = sum([j['time'] for (j, _) in xs])
  print ('Selection covers %.4fs (%.1f%%).' % (tot_sel, (tot_sel / tot) * 100))
  return xs


def z3_times(j):
  return [j2['time'] for (j2, _) in select(lambda nm, _: 'Z3' in nm, j)]


def spine_conss(j):
  xs = []
  def walk(j):
    nm = j['name']
    if nm != 'spine':
      return
    cons = [c for c in j['contents'] if c.get('name') == 'constraints']
    time = j['time']
    xs.append((time, [c['time'] for c in cons]))
  walk_json(walk, j)
  return xs


def spine_branches(j):
  sbs_ctxts = select(lambda nm, _: nm == 'spine', j)
  return [(j2['time'], [nm.split()[0] for (nm, _) in ctxt if 'branch' in nm])
    for (j2, ctxt) in sbs_ctxts]


def spine_branches_long(j):
  sbs_ctxts = select(lambda nm, _: nm == 'spine', j)
  return [(j2['time'], [(nm.split()[0], i) for (nm, i) in ctxt if 'branch' in nm])
    for (j2, ctxt) in sbs_ctxts]


def compare_to(j1, j2, context, res):
  res.append(('pair', context, '', time(j1), time(j2)))
  names = set([j['name'] for j in j1.get('contents', []) + j2.get('contents', [])])
  for name in names:
    j1_xs = [j for j in j1.get('contents', []) if j['name'] == name]
    j2_xs = [j for j in j2.get('contents', []) if j['name'] == name]
    if len(j1_xs) != len(j2_xs):
      res.append(('structure mismatch', context,
          '%s: %d vs %d' % (name, len(j1_xs), len(j2_xs)),
          sum([time(j) for j in j1_xs]),
          sum([time(j) for j in j2_xs])))
    elif len(j1_xs) > 1:
      for (i, (a, b)) in enumerate(zip(j1_xs, j2_xs)):
        context2 = context + ['%s(%d)' % (name, i)]
        compare_to(a, b, context2, res)
    else:
      compare_to(j1_xs[0], j2_xs[0], context + [name], res)

def fun_key(f):
  return '_'.join(f['details'].split('_')[:-1])

def compare_funs(funs1, funs2):
  res = []
  funs1_opts = [(fun_key(f), f) for f in funs1]
  funs2_opts = [(fun_key(f), f) for f in funs2]
  for k in set([k for (k, _) in funs1_opts + funs2_opts]):
    fs1 = [f for (k2, f) in funs1_opts if k2 == k]
    fs2 = [f for (k2, f) in funs2_opts if k2 == k]
    if len(fs1) > 1 or len(fs2) > 1:
      print('Multiple copies of function "%s", skipping' % k)
    elif not fs1:
      print('Function "%s" (%.4fs) not in rhs.' % (k, time(fs2[0])))
    elif not fs2:
      print('Function "%s" (%.4fs) not in rhs.' % (k, time(fs1[0])))
    else:
      print('Comparing function times for "%s".' % k)
      compare_to(fs1[0], fs2[0], [k], res)
  return res

def fudge_compare_time(tm1, tm2):
  '''returns something in range of abs(tm1 - tm2), but then reduces that if
  tm1 and tm2 are similar to avoid just reporting large times that vary little.'''
  if tm1 + tm2 < 0.01:
    return 0.0
  return ((tm1 - tm2) * (tm1 - tm2)) / (tm1 + tm2)

def report_compare(res, n = 10):
  if not res:
    return
  res = [(fudge_compare_time(tm1, tm2), nm, ctxt, detail, tm1, tm2)
    for (nm, ctxt, detail, tm1, tm2) in res]
  res.sort()
  sel = list(reversed(res[- n:]))
  print('Discrepancies (%d of %d):' % (len(sel), len(res)))
  for (_, nm, ctxt, detail, tm1, tm2) in sel:
    print('%s in %s(%s): %.4fs vs %.4fs' % (nm, ctxt, detail, tm1, tm2))


def main():
  import sys
  # FIXME: use argparse or whatever
  if len(sys.argv) >= 4 and sys.argv[1] == 'cmp':
    if sys.argv[2] == '-n':
      n = int(sys.argv[3])
      fs = sys.argv[4:6]
    else:
      n = 15
      fs = sys.argv[2:4]
    assert len(fs) == 2, (fs, sys.argv)
    (f1, f2) = fs
    funs1 = load_funs(f1)
    funs2 = load_funs(f2)
    report_compare(compare_funs(funs1, funs2), n)
  else:
    print('args not understood')
    print('usage e.g. python <nm.py> cmp -n 20 log_time1.txt log_time2.txt')

if __name__ == '__main__':
  main()


'''
# run these interactively to play around
fname = get_fname()

fname = 'log_times.txt'

j = json.load(open(fname))

tot = time(j)
tot

ts = z3_times(j)
ts.sort()
ts

scs = spine_conss(j)
scs.sort()
scs

sbs = spine_branches(j)
sbs.sort()
sbs

sbs_summ = [(t, ','.join([nm[0] for nm in nms])) for (t, nms) in sbs[-40:]]
sbs_summ

sbs = spine_branches_long(j)
sbs.sort()
sbs[-3:]

'''

