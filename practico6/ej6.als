open util/ordering [ State ]
sig State{}
sig Label{}
sig LabelledTransition{
	transition: State -> State
	label: one Label
}
sig LTS{
	states: set State
	transitions: set LabelledTransition
}

fact reachability {
	all s: State, l:LTS | let s0 = first[] | s0->s in ^(l.transitions.transition)    
}

pred simulation[lts:LTS, rel:LTS->LTS]{
	~rel.(lts.transitions) in (lts.transitions).~rel
}

pred bisimulation[lts:LTS, rel:LTS->LTS]{
	~rel.(lts.transitions) in (lts.transitions).~rel and
	rel.(lts.transitions) in (lts.transitions).rel

}

pred weak_bisimulation[lts:LTS, rel:LTS->LTS]{
	//~rel.(lts.transitions) in (lts.transitions).~rel
}

assert Bi_is_sim{
	all lts: LTS, rel: LTS->LTS | 
	bisimulation[lts, rel] implies simulation[lts,rel]
}

assert Weak_is_bi{
	all lts: LTS, rel: LTS->LTS | 
	weak_bisimulation[lts, rel] implies bisimulation[lts,rel]
}

assert Comp_sim{
	all lts: LTS, rel, rel': LTS->LTS | 
	simulation[lts, rel] and simulation[lts, rel'] 
	implies simulation[lts,rel.rel']
}

assert Comp_wsim{
	all lts: LTS, rel, rel': LTS->LTS | 
	weak_bisimulation[lts, rel] and weak_bisimulation[lts, rel'] 
	implies weak_bisimulation[lts,rel.rel']
}
