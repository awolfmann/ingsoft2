open util/ordering [ Book1 ]
abstract sig Target {}
sig Addr1 extends Target {}
abstract sig Name1 extends Target {}
sig Alias, Group extends Name1 {}
sig Book1 {
	 names: set Name1,
	 addr: names -> some Target }
	 {
	 no n: Name1 | n in n.^(addr)
	 all a: Alias | lone a.addr
	 }
pred add1 (b, b': Book1, n: Name1, t: Target) {b'.addr = b.addr + n -> t}
pred del1 (b, b': Book1, n: Name1, t: Target) {b'.addr = b.addr - n -> t}
fun lookup1 (b: Book1, n: Name1): set Addr1 {n.^(b.addr) & Addr1}
assert delUndoesAdd1 {
	 all b,b',b'': Book1, n: Name1, t: Target |
		 no n.(b.addr) and
			 add1 [b,b',n,t] and del1 [b',b'',n, t] implies b.addr = b''.addr
	 }
// check delUndoesAdd1 for 3
assert addIdempotent1 {
	 all b,b',b'': Book1, n: Name1, t: Target |
		 add1 [b,b',n,t] and add1 [b',b'',n,t] implies b'.addr = b''.addr
	 }
// check addIdempotent1 for 3
assert addLocal1 {
	 all b,b': Book1, n,n': Name1, t: Target |
		 add1 [b,b',n,t] and n != n'
			 implies lookup1 [b,n'] = lookup1 [b',n']
	 }
// check addLocal1 for 3 but 2 Book1
assert lookupYields {
	 all b: Book1, n: b.names | some lookup1 [b,n]
	 }
// check lookupYields for 4 but 1 Book1

pred init [ b:Book1 ] { 
	no b.names and 
	no b.addr
}

fact Traces {
	init[first[]]
	all b: Book1, b':next[b] |
	(some n:Name1, t:Target | add1[b,b',n,t])
	or
	(some n:Name1| some lookup1[b,n] and b = b')
}
pred Consistent[b:Book1, n:Name1, t:Target]{
	let t1 = lookup1[b,n] | some t1 implies t1=t
}
assert C{
	all b:Book1 |some n: b.names | let t = n.(b.addr)| Consistent[b,n, t]
}
check C for 3
