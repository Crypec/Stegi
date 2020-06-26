
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
	#ausgabe("{}", fib(20))
}
