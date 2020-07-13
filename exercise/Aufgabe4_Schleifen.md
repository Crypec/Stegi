## Aufgaben 4: Schleifen

<strong> Wissenwertes über Schleifen: </strong><BR>
Wenn Sie in einem Programm eine oder mehrere Anweisungen öfters wiederholen 
möchten und die Anzahl der Wiederholungen nicht von anfang an feststeht braucht man
sogenannte Schleifen. <BR>
Schleifen haben einen besonderen Aufbau, sie besitzen jeweils eine Schleifenbedingung
und einen Schleifenrumpf, welcher die zu wiederholenden Befehle enthält.<BR>
Die Schleifenbedingung überprüft, ob die Anweisungen wiederholt werden (also ob die Bedingung
weiterhin <strong>wahr</strong> ist) oder nicht. <BR>
Man unterscheidet in STGI zwischen 2 Arten von Schleifen. Beide Arten sind Kopfgesteuert, dass 
bedeutet, dass die Bedingung in den Schleifenkopf geschrieben wird. 
<BR>
Schleifen überprüfen <strong>vor</strong> jedem Schleifendurchlauf, ob die Bedingung 
weiterhin unerfüllt ist oder nicht.
<BR>
<BR>
Endlosschleifen haben eine nie endende Bedingung und bringen gerne mal das Programm zum
Abstürzen: Hier ist also Vorsicht geboten! Vor allem Anfänger kreieren gerne ausversehen
Endlosschleifen.
<BR>
<BR>
<strong>Für-Schleife (Zählschleife)</strong> <BR>
Bei der Zählschleife steht im Schleifenkopf die Bedingung, zusätzlich kann man
im Kopf eine Variable initialisieren, die nur in der Schleife gilt. Die Anweisungen
stehen im Schleifenrumpf.

Beispiel:
  
```go
fuer i := 0 bis 10 {
    #ausgabe("i")
  //Anweisung
}
```

<strong>Solange-Schleife</strong> <BR>
Die Solange-Schleife hat die Bedingung ebenfalls im Schleifenkopf, jedoch muss jede Variable 
die in der Bedingung benutzt wird, vorher initialisiert werden. Die Anweisungen
stehen hierbei im Schleifenrumpf. <BR>
Beispiel: <BR>
```go
solange bedingung {
    //Aktion 
}
```


#### Aufgaben: <BR>
Legen Sie ein neues Projekt mit dem Namen "Aufgabe 4" an.<BR>

a) Testen Sie verschiedene Bedingungen wie "wahr", (<=,=>,>,<,=,) etc. aus. Was fällt Ihnen auf?<BR>

b) Testen Sie jeweils für beide Schleifenarten das selbe aus 
und stellen Sie Unterschiede fest.<BR>

c) Was passiert, wenn Sie die Variable im Schleifenrumpf mit 1 addieren oder subtrahieren, während
die Variable i hochzählt?<BR>

d) Bauen Sie nun die folgende Schleife in das Programm ein:

```go
fuer i := 0 bis 10 {
    fuer j := 0 bis i {
        #ausgabe("*")
    }
}
```
Was fällt Ihnen auf? In welcher Form beeinflussen die Variablen i und j das Programm?
Welche Rolle spielen die Endwerte von i und j?

e) Versuchen Sie andere Formen durch Schleifen auszugeben.<BR>
Zum Beispiel: <BR>
* Ein Rechteck
* Ein rechtwinkliges Dreieck, mit der geraden Kante auf der rechten Seite
* Ein gleichschenkliges/symetrisches Dreieck

               