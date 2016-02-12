open util/ordering [ System ]

sig Addr {}
sig Data {}

sig Memory {
	addrs: set Addr,
	map: Addr -> one Data
}

sig MainMemory extends Memory { }
sig Cache extends Memory {
	dirty: set addrs
}
sig System {
	cache: Cache,
	main: MainMemory
}
//fact {
//	no (MainMemory & Cache)
//}

pred Write [m,m': Memory, d: Data, a: Addr] {
	m'.map = m.map ++ (a -> d)
}
pred Read [ m: Memory, a: Addr, d: Data ] {
    let d' = m.map[a] | some d' implies d = d'
}

pred Load[m:MainMemory, c,c': Cache, a:Addr]{
	c'.map = c.map ++ (a->m.map[a])
	c'.dirty = c.dirty
	
}

pred Flush[m,m':MainMemory, c,c':Cache]{
	m'.map =  m.map ++ (c.dirty -> c.map[c.dirty])
	c'.dirty = none 
}

pred WriteSys [s,s':System,  d: Data, a: Addr ]{
	s'.cache.map = s.cache.map ++ (a->d) and 
	s'.cache.dirty = s.cache.dirty ++ a and
	s'.main=s.main
}
pred ReadSys[s,s':System, a:Addr, d:Data]{
	Read[s.cache, a,d] and s=s'
	or  
	(Load[s.main, s.cache, s'.cache, a] and Read[s'.cache, a,d]) 
}

pred Consistent [s:System] {
	s.cache.map - (s.cache.dirty -> Data) = s.main.map
}

pred init [ s: System ] { no s.main.map and 
	no s.cache.map and 
	no s.cache.dirty 
}


fact SystemTransition{
	init[first[]]
	all s:System, s':next[s] |
		(some d:Data,a:Addr| WriteSys[s,s', d,a])
		or (Flush[s.main, s'.main, s.cache, s'.cache])
		or (some d:Data, a:Addr | ReadSys[s,s',a,d])
}

assert C {
	all s:System | Consistent[s]  
}

check C for 3
