Typ Person {
	name: Text,
	alter: Zahl,
}

impl Person {
	// fun neu() -> Person {
	// 	rueckgabe Person {
	// 		name: "Simon",
	// 		alter: 18,
	//          };
	// }

	fun darf_fahren(foo: Zahl) -> Bool {
		rueckgabe foo >= 18;
	}
}



fun fib(n: Zahl) -> Zahl {
	wenn n gleich 0 dann {
		rueckgabe 0
	} sonst wenn n gleich 1 dann {
		rueckgabe 1
	} sonst {
		rueckgabe fib(n-1) + fib(n-2)
    }
}

fun Start() {
	simon := Person::neu()
	#ausgabe("{}", simon)
	fuer b := 0 bis 10 {
		#ausgabe("{}", b)
	}
}