
fn test(x: Zahl) -> Zahl {

	wenn x gleich 2 dann {
		#ausgabe("x ist gleich 2")
		rueckgabe x * 4
	} sonst wenn x gleich 3 dann {
		rueckgabe x * 20;
	} sonst {
		rueckgabe x * 400;
	}

	rueckgabe;
}


fun fib(x: Zahl) -> Zahl {
	wenn x <= 1 dann {
		rueckgabe x
	}
	rueckgabe fib(x -1) + fib(x - 2)
}

fun Start() {
	#ausgabe(fib(4))
}
