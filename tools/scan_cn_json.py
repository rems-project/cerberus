# for reading the JSON (ish) timing output 

import json


fname = 'time_log.txt'
j = json.load(open(fname))


def time(j):
  if 'time' in j:
    return j['time']
  return sum([time(j2) for j2 in j.get('contents', [])])

tot = time(j)
tot


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

ts = z3_times(j)

ts.sort()
ts

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

scs = spine_conss(j)

scs.sort()
scs


def spine_branches(j):
  sbs_ctxts = select(lambda nm, _: nm == 'spine', j)
  return [(j2['time'], [nm.split()[0] for (nm, _) in ctxt if 'branch' in nm])
    for (j2, ctxt) in sbs_ctxts]

sbs = spine_branches(j)
sbs.sort()
sbs

sbs_summ = [(t, ','.join([nm[0] for nm in nms])) for (t, nms) in sbs[-40:]]
sbs_summ


def spine_branches_long(j):
  sbs_ctxts = select(lambda nm, _: nm == 'spine', j)
  return [(j2['time'], [(nm.split()[0], i) for (nm, i) in ctxt if 'branch' in nm])
    for (j2, ctxt) in sbs_ctxts]

sbs = spine_branches_long(j)
sbs.sort()
sbs[-3:]







