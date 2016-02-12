sig Node {}

sig Graph {
	nodes: set Node,
	edges:  nodes -> nodes
}



// aciclico: si la clausura transitiva de las aristas intersec iden = none
pred acyclic[g:Graph]{
	//^(g.edges) & iden = none
	 no(^(g.edges) & iden)
} 

//run acyclic for 3 but 1 Graph

// no dirigido si estan todas las aristas para ambos lados
pred undirected [g:Graph]{
	(g.edges) = ~(g.edges)
}

// run undirected for 3 but 1 Graph
 

// si para cada par de vértices u y v existe un camino de u hacia v y un camino de v hacia u
pred hard_conex [g:Graph]{
	all u,v : g.nodes |
	(u->v) in ^(g.edges) and
	(v->u) in ^(g.edges)
}

// run hard_conex for 3 but 1 Graph

pred conex [g:Graph]{
	g.nodes -> g.nodes = ^ (g.edges + ~(g.edges))
}

// run conex for 3 but 1 Graph

pred comp_hard_conex [g:Graph]{
	some u,v : g.nodes |
	(u->v) in ^(g.edges) and
	(v->u) in ^(g.edges)
}
run comp_hard_conex for 5 but 1 Graph

pred comp_conex [g:Graph]{
	some u,v : g.nodes |
	(u->v) in ^(g.edges) or
	(v->u) in ^(g.edges)
}

