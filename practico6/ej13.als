sig Node {}
sig Tree{
	root: one Node,
	nodes: set Node,
	child:  nodes -> nodes
}

pred d[t:Tree]{ // no puede haber aristas dirigidas hacia la raiz
	no(t.root.~(t.child))
}
pred r[t:Tree]{ // debe haber un camino dirigido de la raiz a todo nodo
	all n:Node - t.root | (t.root->n) in ^(t.child)
}
pred q[t:Tree]{ //no puede tener 2 padres
	no (t.child.(~(t.child)) - iden)
}

pred tree[t:Tree]{
	d[t] and r[t] and q[t] 
}

run tree for 5 but 1 Tree

