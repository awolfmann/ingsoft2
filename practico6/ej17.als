sig Node {}

sig WGraph {
	nodes: set Node,
	edges:  nodes -> Int ->nodes
}
