# Stegi

![Stegi Dinosaurier Logo]
(https://github.com/Crypec/Stegi/stegi_logo.jpg)

## Stegi installieren
Stegi ist in der Progammiersprache [Rust](https://www.rust-lang.org/) geschriben. Du musst also eine Version des Rustkompilers auf deinem System installieren.
Danach kannst du dieses Repository mit [git](https://git-scm.com/) klonen.
``` bash
git clone git@github.com:Crypec/Stegi.git
cd stegi
```

Wenn du cargo, das ist das "Buildsystem von Rust" installiert hast kannst du einfach den folgenden Befehl laufen lassen:
```bash
cargo build -- release # Die '--release' Flagge ist optional, macht den Kompiler aber um einiges schneller
```
## Benutzung
```bash
stegi start # kompiliert dein programm und laesst es gleich laufen.
```