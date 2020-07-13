## Aufgaben 2: Variabeln

Legen Sie ein neues Projekt mit dem Namen "Aufgabe 2" an.<BR>

Bevor Sie anfangen ein paar wichtige Fachbegriffe die man später benötigt:

Deklarieren: Das bedeutet das man die Variable das erste mal "Erwähnt" ohne ihr einen Wert zu zuweisen. Dies ist bei STGI jedoch nicht erlaubt, denn man muss der Variable IMMER einen Wert zuweisen!<BR>
Initialisieren: Initialisieren bedeutet, das man die Variable Deklariert und ihr einen Wert zuweist.<BR>
````go
//Beispiel
n:zahl = 0 // Initialisierung!
n:zahl    // Deklaration, aber NICHT erlaubt!
````
Jetzt wissen Sie wie man Variabeln erzeugt, schreiben Sie nun folgendes Programmm:
````go
Start:= fun () {
    #ausgabe ("Hallo Welt!")
    
    x: Zahl = 10
    y: Zahl = 2
    
    //Addition
    #ausgabe("{}", x + y )
    #ausgabe("{} + {}",x,y)
    
    //Subtraktion
    #ausgabe("{}, x - y")
    #ausgabe("{} - {}", x, y)
}

````
Achten Sie vor allem darauf geöffnete Klammern auch wieder zu schließen! 
Kompilieren Sie und führen Sie nun das Programm aus.

####Aufgaben:<BR>
a) Was passiert beim Ausführen des Programms?<BR>
b) Was machen die einzelnen Ausgaben?<BR>
c) Vertauschen sie bei den Ausgaben die Variabeln hinter dem Komma!<BR>
d) Versuchen Sie auch andere Rechenoperatoren (*, /)<BR>
e) Was geschiet bei besonders großen Zahlen und sehr langen Nachkomastellen?<BR>
        -> Wie genau sind die Rechnungen unter dieser Bedingungen?<BR>
f) Versuchen Sie eine Eingabe wie folgt und experimentieren sie damit:<BR>
````
    #eingabe("Drücken Sie Enter: ") 
    n := #eingabe("Gib eine Zahl ein: ")
    #ausgabe("Ihre Zahl war: {}", n)
````
