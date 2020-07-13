fun Start() {
	simon := Person::neu("Simon", 19);
	kunz := Familie::neu();
	#ausgabe("{}", kunz.duerfen_fahren())
	#ausgabe("{}", simon.darf_fahren())
}

Typ Person {
	name: Text,
	alter: Zahl,
}

Typ Familie {
	personen: [Person],
}

impl Familie {
	 fun neu() -> Familie {
	 	 rueckgabe Familie {
		 		   personen: [
				   			 Person::neu("Simon", 19),
				   			 Person::neu("Simon", 19),
				   			 Person::neu("Simon", 19),
				   ],
		 };
	 }
	 fun duerfen_fahren(selbst) -> [Bool] {
	 	 res := [falsch, falsch, falsch]
		 fuer i := 0 bis 3 {
		 	  res[i] = selbst.personen[i].darf_fahren()
		 }
		 rueckgabe res
	 }
}

impl Person {
	fun neu(name: Text, alter: Zahl) -> Person {
		rueckgabe Person {
			name: name,
			alter: alter,
		};
	}

	fun darf_fahren(selbst) -> Bool {
		rueckgabe selbst.alter >= 18
	}
}

