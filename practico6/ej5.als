open util/ordering[Set] 
sig Element {}

sig Set {
	elements: set Element,
	orden: elements->elements
}


// preorden
pred preorder[s:Set]{
	iden in s.orden and //reflexiva
	^(s.orden) in s.orden			//transitiva
}
run preorder for 3 but 1 Set

// orden parcial
pred partial_order[s:Set]{
	(iden in s.orden) and //reflexiva
	(^(s.orden) in s.orden)	and		//transitiva
	(~(s.orden) & s.orden in iden) //antisimetrica
}

// orden total
pred total_order[s:Set]{
	(iden in s.orden) and //reflexiva
	(^(s.orden) in s.orden)	and		//transitiva
	(~(s.orden) & s.orden in iden) and  //antisimetrica
	(s.orden + ~(s.orden)) = univ->univ //total
}

// orden estricto
pred strict_order[s:Set]{
	no(iden & s.orden) and //irreflexiva
	(^(s.orden) in s.orden)	and		//transitiva
	(~(s.orden) & s.orden in iden) and  //antisimetrica
	(s.orden + ~(s.orden)) = univ->univ //total
}

pred first_elem[s:Set]{
	first.elements = Element
}
run first_elem for 3 but 1 Set

pred last_elem[s:Set]{
	last.elements = Element
}


assert total_is_partial{
	all s:Set | total_order[s] implies partial_order[s] 
}

assert partial_have_first{
	all s:Set | partial_order[s] implies first_elem[s] 
}

assert total_first_last{ 
	all s: Set, x,y: Element | total_order[s] and x = first[] and y = last[] and x!=y
}

assert strict_union{
	all s, s': Set | strict_order[s] and strict_order[s'] implies strict_order[(s+s')]
}

assert strict_composition{
	all s, s': Set | strict_order[s] and strict_order[s'] implies strict_order[(s.s')]
}
