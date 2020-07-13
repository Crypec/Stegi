## Aufgabe 1: Hallo Welt
Das Programm "Hallo Welt" ist ein sehr einfaches Programm, welches zeigen soll wie die Programmiersprache STGI aufgebaut ist. Dieses Programm soll lediglich erstmal die Worte "Hallo Welt" ausgeben :)

Legen Sie ein neues Projekt mit dem Namen "Aufgabe 1" an.<BR>

Um ein neues Projekt anzulegen, geben folgende Befehle in die Kommandozeile ein.
```bash
stegi neu Aufgabe1
stegi start 
```

Schreiben Sie nun folgendes Programm: 
````]
Start:= fun () {
    #ausgabe ("Hallo Welt!")
}
````
Achten Sie vor allem darauf, geöffnete Klammern auch wieder zu schließen! 
Kompilieren Sie mit dem Befehl "stegi start" das Projekt und betrachten Sie die Ausgabe. 


####Aufgaben: <BR> 
Diese Aufgaben sollen Ihnen nicht nur helfen, die Grundlagen besser zuverstehen, sondern Sie auch dazu bringen zu Experimentieren. Denn das ist nicht nur erlaubt, es ist ein muss um Fortschritte zu machen.

Wenn Sie Dinge in Ihrem Programm mit Notizen versehen wollen, können Sie Kommentare benutzen:<BR> 
Kommentare haben immer folgenden Präffix: // Dies ist ein Kommentar 

a) Was geschiet beim Ausführen des Programms?<BR>
b) Bauen Sie weitere Ausgaben ein, was passiert, wenn Sie die hochgestellten Anführungszeichen  weglassen?  
c) Was passiert wenn Sie eine Rechnung in hochgestellten Anführungszeichen schreiben? Was passiert wenn Sie diese weglassen? <BR>
z.B: 
````go
Start := fun() {
    #ausgabe("Hallo Welt!")
    #ausgabe("3+10") // mit hochgestellten Anführungszeichen
    #ausgabe("{}", 3+10) //ohne hochgestellte Anführungszeichen
}
````
d) Was ist der Unterschied zwischen Textausgaben und Zahlen/Rechnungen?<BR>
e) Wo braucht man die hochgestellten Anführungszeichen, wovon hängt es ab?(Bei welchen Typen sind sie notwendig?)<BR>
f) Erzeugen Sie (Initialisiere) eine Variable wie unten gezeigt, gebe Sie dann wie folgt aus:
````java
Start := fun() {
    a : Zahl = 2
    #ausgabe("a hat den Wert {}!", a)

    a := 2 // Was geschiet jetzt? 
    #ausgabe("a hat den Wert {}!", a)
}
````
g) Was passiert wenn Sie das Programm ausführen? Versuchen Sie es mit anderen Beispielen und mehreren Variablen!

Wenn Sie die Basics nochmal nachlesen wollen folgen Sie folgendem Link: 
"LINK PLATZHALTER"
