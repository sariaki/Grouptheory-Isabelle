theory "6_Gruppen"

imports "HOL-Algebra.Congruence" "HOL-Library.FuncSet"

begin

section \<open>Einführung\<close>

text \<open>Arbeitsgrundlagen
  \<^item> van der Waerden, Algebra \<^file>\<open>vanDerWaerden55 moderneAlg.pdf\<close>
  \<^item> Gruppentheorie in Isabelle. Tatsächlich wird der Gegenstand doppelt eingeführt:
    \<^item> \<^file>\<open>~~/src/HOL/Algebra/Group.thy\<close>
    \<^item> \<^file>\<open>~~/src/HOL/Groups.thy\<close>
  \<^item> ggf. weitere Skripte zur Einführung in die Gruppentheorie. 
    Man findet diese zahlreich im Internet.
  Zu Isabelle
  \<^item> \<section> 8.3 - 8.3.2, \<^file>\<open>NipkowPaulsonWenzel02 Isabelle_HOL.pdf\<close>
  \<^item> \<section> 1 - 2.1, \<^doc>\<open>locales\<close>
  
  Sollte privater Bedarf an einer Gutenachtlektüre bestehen, so lässt sich
  \<^item> Saunders Mac Lane, "Van der Waerden's Modern Algebra" \<^file>\<open>MacLane97 vanDerWaerden_modernAlg.pdf\<close>
  heranziehen\<close>

subsection \<open>Aufträge\<close>

text\<open>
  \<^enum> Formalisierung: Fangt eine eigene formalisierte Theorie zu Gruppen an. 
    Folgt dabei möglichst genau van der Waerden (\<section> 9).
    Beispiele sind dabei nicht zu formalisieren.
    Schaut, wie weit ihr kommt.
    Haltet zumindest in kurzen Kommentaren auch fest, welche Entscheidungen ihr warum getroffen habt.
    Dabei kann die Syntax @{text "..."}, z.B. @{text "f: x \<mapsto> x\<^sup>2"}, helfen.
  Präsentation
  \<^enum> Einführung in Gruppentheorie: Erläutert dem Kurs 
    \<^item> die grundlegende Idee und den Begriff der Gruppe,
    \<^item> wie dies in Isabelle implementiert ist.
    \<^item> Vergleicht dies mit eurem Formalisierungsversuch entlang van der Waerden.
  \<^enum> Present around 3 exercise regarding the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance.
    Die Aufgaben können auch klassische mathematische Arbeitsweise vorsehen. 
    Allerdings sollte mindestens eine Aufgabe auf Isabelle ausgelegt sein.\<close>

section \<open>Erläuterungen\<close>

text\<open>Die Beispiele sollen nur bei der Formalisierung übersprungen werden.
  Lest sie euch trotzdem durch und lasst sie in eure Vorstellung für den Kurs einfließen!
  Hier könnt ihr auch andere Skripte, die eine Einführung in die Gruppentheorie bieten zum Vergleich 
  heranziehen.

  In \<^file>\<open>~~/src/HOL/Algebra/Group.thy\<close> werden nicht Gruppen, sondern eigentlich Monoide als grundlegende Struktur eingeführt.
  Monoide sind eine noch rudimentärere algebraische Struktur, die wie Gruppen auf einer Grundmenge 
  definiert sind.
  Insgesamt sieht der Aufbau folgendermaßen: Zunächst wird ein record monoid definiert, der folgendes 
  umfasst:
  \<^enum> einen "carrier", d.h. eine Menge von Elementen von Typ 'a
  \<^enum> eine Verknüpfung "mult", d.h. eine Operation vom Typ carrier \<times> carrier \<rightarrow> carrier
  \<^enum> ein "unit"-Element e.
  Dann wird eine Menge (zweiseitiger) Einheitselemente definiert (d.h. eine Element x zu dem es ein
  Inverses x\<inverse> mit x x\<inverse> = x\<inverse> x = e gibt) is defined.
  Schließlich wird ein locale group definiert, das annimmt, dass alle Elemente in der Grundmenge 
  auch Einheitselemente sind.

  Daneben wird die Gruppenstruktur in \<^file>\<open>~~/src/HOL/Groups.thy\<close> nur über Locales eingeführt.
  Ich würde aber empfehlen, den erstgenannten Weg als Grundlage für das Projekt zu wählen.\<close>

text \<open>
  Was damit gemeint ist, dem Text van der Waerdens möglicht genau zu folgen, wird vielleicht am 
  besten an einem Beispiel erläutert: 
  Wenn er von einer "nicht leeren Menge \<GG> von Elementen irgendwelcher Art (z.B. von Zahlen, von 
  Abbildungen, von Transformationen)" schreibt, dann sollte bemerkt werden, das dieses dazu passt, 
  dass in Isabelle die partial_object's jeweils bzgl. eines gewissen Typs definiert sind und nicht,
  wie neuere Skripte nahelegen einfach Mengen von einem "Universaltyp" sind.\<close>
  
text \<open>Mengenlehre kann vorausgesetzt werden. 
  Entsprechend sind die HOL-Bibliotheken "FuncSet" und "Congruence" bereits importiert.
  Sollten weitere Sachen in van der Waerdens text vorausgesetzt werden, so können auch dazu Theorien
  importiert werden.

  Dieses Projekt unterscheidet sich von anderen dahingehend, dass Umfang und Ziel weniger eindeutig 
  bestimmt sind und mehr Freiheit bei der Umsetzung besteht.\<close>

section \<open>Versuch der Formalisierung von van der Waerden\<close>

record 'a group =
  carrier :: "'a set"
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  unit :: "'a"


end