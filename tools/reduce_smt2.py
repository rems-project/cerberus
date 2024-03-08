''' parse a z3 log, remove completed push/pop pairs '''

import re

paren_re = re.compile(r"(\(|\))")

def parse_s_expressions(ss):
        bits = [bit for s in ss for split1 in paren_re.split(s)
                for bit in split1.split ()]
        def group(n):
                if bits[n] != '(':
                        return (n + 1, bits[n])
                xs = []
                n = n + 1
                while bits[n] != ')':
                        (n, x) = group(n)
                        xs.append(x)
                return (n + 1, tuple(xs))
        n = 0
        xs = []
        while n < len(bits):
                (n, x) = group(n)
                xs.append(x)
        return tuple(xs)

def flat_s_expression (s):
        if type(s) == tuple:
                return '(' + ' '.join (map (flat_s_expression, s)) + ')'
        else:
                return s

def parse_file(fname):
        sexps = parse_s_expressions(open(fname))
        sys.stderr.writelines(['Parsed %s: %d elements.\n' % (fname, len(sexps))])
        return sexps

move_checks_down = False

def redux_push_pop_sexps(sexps):
        stack = [([], [])]
        for sexp in sexps:
                if sexp[:1] == ('push', ):
                        (_, n) = sexp
                        n = int(n)
                        for i in range(n):
                                stack.append(([], []))
                elif sexp[:1] == ('pop', ):
                        (_, n) = sexp
                        n = int(n)
                        for i in range(n):
                                stack.pop()
                elif move_checks_down and sexp[:1] == ('check-sat', ):
                        stack[-1][1].append(sexp)
                else:
                        stack[-1][0].append(sexp)
        defs = tuple([x for (def_chunk, _) in stack for x in def_chunk])
        checks = tuple([x for (_, check_chunk) in stack for x in check_chunk])
        sys.stderr.writelines(['Filtered, %d defs, %d checks.\n' % (len(defs), len(checks))])
        return (defs, checks)

def tok_set(sexp):
        xs = [sexp]
        ss = set()
        while xs:
                x = xs.pop()
                if type(x) == tuple:
                        xs.extend(x)
                else:
                        ss.add(x)
        return ss

def redux_def_sexps(sexps):
        toks = set()
        res = []
        for x in reversed(sexps):
                if x[:1] == ('declare-fun', ):
                        (_, nm, typ, _) = x
                        if nm not in toks:
                                continue
                if x[:1] == ('define-fun', ):
                        (_, nm, typ, _, body) = x
                        if nm not in toks:
                                continue
                if x[:1] == ('declare-datatypes', ):
                        (_, tys, constrs) = x
                        nms1 = [nm for dt in tys for (nm, arity) in tys]
                        nms2 = [nm for dt in constrs for app in dt for nm in app[:1]]
                        nms3 = [nm for dt in constrs for app in dt for (nm, ty) in app[1:]]
                        nms = nms1 + nms2 + nms3
                        assert(all([type(nm) == str for nm in nms]))
                        if not [nm for nm in nms if nm in toks]:
                                continue
                toks.update(tok_set(x))
                res.append(x)
        sys.stderr.writelines(['Dropped redundant declarations, %d sexps.\n' % (len(res))])
        return tuple(reversed(res))

def name_asserts(sexps):
	toks = tok_set(tuple(sexps))
	i = 1
	for tok in toks:
		if tok.startswith('?assert_'):
			j = int(tok.split('_')[1])
			i = max(i, j + 1)
	res = []
	for x in sexps:
		if x[:1] != ('assert', ):
			res.append(x)
			continue
		toks = tok_set(x)
		if ':named' in toks:
			res.append(x)
			continue
		res.append(('assert', ('!', x[1], ':named', '?assert_%d' % i)))
		i += 1
	return res

def drop_unused_named_asserts(assert_set, sexps):
	res = []
	for x in sexps:
		if x[:1] != ('assert', ):
			res.append(x)
			continue
		if x[1][0] == '!' and x[1][2] == ':named':
			(_, _, _, name) = x[1]
			if name not in assert_set:
				continue
		res.append(x)
	return res

def print_sexps(sexps):
        for sexp in sexps:
                print(flat_s_expression(sexp))

import sys

fname = sys.argv[1]

sexps = parse_file(fname)

(defs, checks) = redux_push_pop_sexps(sexps)

res = defs + checks

assert_set = []
# assert_set = set('?assert_48 ?assert_50 ?assert_52 ?assert_53 ?assert_54 ?assert_63 ?assert_64 ?assert_113 ?assert_117 ?assert_118 ?assert_121 ?assert_124 ?assert_133 ?assert_136 ?assert_182 ?assert_183 ?assert_185 ?assert_188 ?assert_189 ?assert_194 ?assert_202'.split())
if assert_set:
	res = drop_unused_named_asserts(assert_set, res)

res = redux_def_sexps(res)

# FIXME: do command-line parsing or otherwise configurable
if True:
	res = name_asserts(res)

print_sexps(res)







