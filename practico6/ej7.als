sig Interprete {}
sig Cancion {}
sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	canciones.interpretaciones in interpretes
	interpretaciones.interpretes in canciones
	//~interpretaciones.interpretaciones in iden
	//interpretaciones.interpretes = interpretes
}

pred add[c, c': Catalogo, s: Cancion, i:Interprete ]{
	c'.interpretaciones = c.interpretaciones + s->i
	//agregar c'.canciones = c.canciones + s 
	// y c'.interpretes = c.interpretes + i? 
}

pred delete[c, c': Catalogo, s: Cancion, i:Interprete ]{
	c'.interpretaciones = c.interpretaciones - s->i
}

fun inter [c: Catalogo]: Interprete -> Interprete {
	~(c.interpretaciones).(c.interpretaciones) - iden
}

//pred showInter[c: Catalogo]{
//	inter[c]
//}

run add for 3 but 3 Catalogo

