open util/ordering[State] 

// El dominio del problema ---------

abstract sig Person{time:Int}
one sig IJ, Novia, Padre, Suegro extends Person{}
//one sig IJ extends Person {time: 5}
//one sig Novia extends Person {time: 10}
//one sig Padre extends Person {time: 20}
//one sig Suegro extends Person {time: 25}

fact times { IJ.time=5 and Novia.time = 10 and
	Padre.time=20 and Suegro.time = 25
 }

// La dinámica --------------------
// Espacio de estado

sig State {
	near: set Person, 
	far: set Person,
	elapsed: Int 
	} 

// Estado inicial

fact initialState {
	let s0 = first[] | s0.near = Person and no s0.far and s0.elapsed=0 
}

// Transición

pred crossBridge [ from, from', to, to': set Person, t, t':Int ] { 
	( from' = from - IJ && to' = to + IJ and t' = t.plus[IJ.time]) 
	||
	( some item: from - IJ |
		from' = from - IJ - item &&
		to' = to + IJ + item &&
		t' = t.plus[item.time]
		)
	} 

fact stateTransition {
	all s: State, s': next[s] |
		( IJ in s.near => crossBridge [ s.near, s'.near, s.far, s'.far, s.elapsed, s'.elapsed] )
		&&
		( IJ in s.far => crossBridge [ s.far, s'.far, s.near, s'.near, s.elapsed, s'.elapsed ] )
}

// Estado Final

pred solvePuzzle[] {
	last[].far = Person and
	last[].elapsed <= 60
	 
}

// Ejecución

run solvePuzzle for 10 State
