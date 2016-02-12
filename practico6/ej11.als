sig Name, Addr {}
sig Book {addr: Name -> lone Addr}
pred show (b: Book) {
	 #b.addr > 1
	 #Name.(b.addr) > 1
	 }
run show for 3 but 1 Book
pred add (b, b': Book, n: Name, a: Addr) {b'.addr = b.addr + n -> a}
pred del (b, b': Book, n: Name) {b'.addr = b.addr - n -> Addr}
fun lookup (b: Book, n: Name): set Addr {n.(b.addr)}
pred showAdd (b, b': Book, n: Name, a: Addr) {
	 add [b, b', n, a]
	 #Name.(b'.addr) > 1
	 }
run showAdd for 3 but 2 Book
assert delUndoesAdd {
	 all b,b',b'': Book, n: Name, a: Addr |
		 no n.(b.addr) and
	 	 add [b,b',n,a] and del [b',b'',n] implies b.addr = b''.addr
	 }
assert addIdempotent {
	 all b,b',b'': Book, n: Name, a: Addr |
		 add [b,b',n,a] and add [b',b'',n,a] implies b'.addr = b''.addr
	 }
assert addLocal {
	 all b,b': Book, n,n': Name, a: Addr |
		 add [b,b',n,a] and n != n'
			 implies lookup [b,n'] = lookup [b',n']
	 }
check delUndoesAdd for 10 but 3 Book
check addIdempotent for 3
check addLocal for 3 but 2 Book

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
check delUndoesAdd1 for 3
assert addIdempotent1 {
	 all b,b',b'': Book1, n: Name1, t: Target |
		 add1 [b,b',n,t] and add1 [b',b'',n,t] implies b'.addr = b''.addr
	 }
check addIdempotent1 for 3
assert addLocal1 {
	 all b,b': Book1, n,n': Name1, t: Target |
		 add1 [b,b',n,t] and n != n'
			 implies lookup1 [b,n'] = lookup1 [b',n']
	 }
check addLocal1 for 3 but 2 Book1
assert lookupYields {
	 all b: Book1, n: b.names | some lookup1 [b,n]
	 }
check lookupYields for 4 but 1 Book1

fun alpha [b1: Book1]: Book {
{ b: Book | b.addr = ^(b1.addr) }
}


