## Aufgabe 3: Pq-Formel

Bevor Sie anfangen können, müssen Sie die Grundlagen der Pq-Formel kennen. 

Eine quadratische Gleichung hat die Normalform 0=ax^2+bx+c, hierbei sind a,b,c reelle Zahlen.
 Die Variable a muss hierbei immer gleich 1 sein. 
 Solche Gleichungen lassen sich mit der sogenannten pq-Formel lösen. 

<BR>
Die Pq-Formel sieht aus wie folgt: 
<BR>
x1/2 = -b/2 +-((b/2)^2-c)^0,5 <BR>


## Aufgaben: <BR>
Legen Sie ein neues Projekt mit dem Namen "Aufgabe 3" an.<BR>
Schreiben Sie nun folgendes Programm:

```go
b := #eingabe("Gib einen Wert für b ein: ")
c := #eingabe("Gib einen Wert für c ein: ")

b := Zahl::von_text(b)
c := Zahl::von_text(c)

x1 := -b/2 + Zahl::wurzel((b/2)*(b/2) - c),2)
x2 := -b/2 - Zahl::wurzel((b/2)*(b/2) - c),2)

#ausgabe("x1: {}, x2: {}", x1, x2) 
```
Kompilieren Sie das Programm und testen Sie folgendes aus:<BR>

a) Gibt es Fälle, bei denen kein Ergebnis möglich ist? Wenn ja, weshalb ist dies so?.<BR>

b) Erweitern Sie ihr Programm so, dass eine Meldung ausgegeben wird, sobald keine Lösung möglich ist.

#### Anmerkung: 
Dieses Programm funktioniert so im Moment noch nicht, da die Standardbibliothek noch nicht komplett ist. Das Arbeitsblatt wird erweitert, sobald die Standardbibliothek vervollständigt ist. Wir arbeiten daran und produzieren im Laufe der Zeit weitere Arbeitsblätter mit interessanten Aufgaben.