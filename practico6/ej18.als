abstract sig List {}
one sig EmptyList extends List {}
sig NonEmptyList extends List {
	 element: Element,
	 rest: List
	 }

fact ListGenerator {
all l: List, e: Element |
		 some l’: List | l’.rest = l and l’.element = e
	 }
