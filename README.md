![Stegi Dinosaurier Logo](https://github.com/Crypec/Stegi/blob/master/stegi_logo.jpg)
# Stegi

> Eine Programmiersprache entwickelt speziell fuer Anfaenger

[![Build Status](https://travis-ci.org/Crypec/Stegi.svg?branch=master)](https://travis-ci.org/Crypec/Stegi)
![Platforms](https://img.shields.io/badge/platforms-Windows%2C%20macOS%20and%20Linux-blue)
![License](https://img.shields.io/github/license/crypec/stegi)
![GitHub release (latest by date)](https://img.shields.io/github/v/release/crypec/Stegi)


## Stegi installieren
Stegi ist in der Progammiersprache [Rust](https://www.rust-lang.org/) geschrieben. Du musst also eine Version des Rustkompilers auf deinem System installieren.
Danach kannst du dieses Repository mit [git](https://git-scm.com/) klonen.
``` bash
git clone git@github.com:Crypec/Stegi.git #Projekt von Github herunterladen.
cd stegi # In das Projektverzeichnis wechseln.
```

Wenn du cargo, das ist das "Buildsystem von Rust" installiert hast kannst du einfach den folgenden Befehl laufen lassen:
```bash
cargo build -- release # Die '--release' Flagge ist optional, macht den Kompiler aber um einiges schneller
```
## Benutzung
```bash
stegi start # kompiliert dein programm und laesst es gleich laufen.
```

## Spezifikation

### Strukturdatentypen
```go
Person := Typ {
	name: Text,
	alter: Zahl,
}
```

### Enumerationsdatentypen
```go
Wochentag := Typ Montag
               | Dienstag
			   | Mittwoch
			   | Donnerstag
			   | Freitag
			   | Samstag
			   | Sonntag
```

### Funktionen
```go
// template
name := fun(parameter: Typ) -> Typ {
	// ...
}


// beispiel
foo := fun(bar: Text) -> Text {
	// ...
}
```

### Implementierungsbloecke
```go
// template
Impl Person {
	darf_fahren := fun(selbst) -> Bool {
		rueckgabe selbst.alter >= 18
	}
}
```

### Variableninitalisierung
```go
// Template
name := wert

// Beispiel 1
a := 4 + 2

// Beispiel 2
a := (b[0] - 3)

// Beispiel 3
a := [0, 1, 2, 3]

// Beispiel 4
simon := Person {
	name: "Simon",
	alter: 18,
};
```

## Variablenzuweisung
```go
// Template
ziel = wert

// Beispiel 1
foo = 20


// Beispiel 2
bar[0] = 20

// Beispiel 3
foo.bar[0] = 20

// Beispiel 4
foo.bar[0].bazz = 20
```
### Fuer-Schleifen
```go
// Eine 'fuer' durchlaueft die Elemente eines Feldes der Reihe nach

liste := [0, 1, 2, 3, 4, 5]
fuer element := liste {
	#ausgabe("{}", element)
}

fuer element := 0 bis 6 {
	#ausgabe("{}", element)
}
```

### Solange-Schleifen
```go
// Eine 'solange' Schleife laeuft solange wie die Bedingung in ihrem Kopf wahr ist

solange bedingung {
	#ausgabe("Endlosschleife!")
}


// Beispiel
a := 0
solange a != 0 {
	a = a - 1
	#ausgabe("Endlosschleife!")
}
```

### Wenn Verzweigungen
```go
wenn bedinung dann {
	// hier geht es weiter
} sonst wenn 2. bedinung {
	// falls der der erste fall nicht, dafuer aber der die 2. Bedingung eintrifft
} Sonst {
	// wenn keine der ersten beiden Bediungen eintritt
}
```
