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
  unit :: "'a" ("e")

definition inverse :: "('a, 'b) group_scheme \<Rightarrow> 'a \<Rightarrow> 'a"
  where "inverse G a = (THE i. i \<in> carrier G \<and> mult G i a = unit G)" \<comment> \<open>a\<inverse> als Variablenname ist nicht erlaubt in Isabelle\<close>
\<comment> \<open>In \<section>9. wird eigentlich erstmal nur von einem linksseitigen inversen Element gesprochen\<close>

definition group_inverse_elements :: "('a, 'b) group_scheme \<Rightarrow> 'a set" where
  "group_inverse_elements G = {a. a \<in> carrier G \<and> (\<exists>b \<in> carrier G. a = inverse G b)}" \<comment> \<open>nicht explizit in v.d.W. Text erwähnt\<close>

locale group =
  fixes G (structure)
  assumes not_empty: "carrier G \<noteq> {}"

  and is_closed [intro, simp]: "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<comment> \<open>Zusammensetzungsvorschrift\<close>
    \<Longrightarrow> mult G a b \<in> carrier G" 

  and is_assoc: "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<comment> \<open>Assoziativgesetz\<close>
    \<Longrightarrow> mult G (mult G a b) c = mult G a (mult G b c)"

  and has_identity [intro, simp]: "unit G \<in> carrier G" \<comment> \<open>Einselement\<close>
  and identity_l [simp]: "a \<in> carrier G \<Longrightarrow> mult G (unit G) a = a"
  and identity_r [simp]: "a \<in> carrier G \<Longrightarrow> mult G a (unit G) = a" \<comment> \<open>In \<section>9. wird eigentlich erstmal nur von einem linksseitigen Einselement gesprochen\<close>

  and group_inverse_all: "carrier G = group_inverse_elements G" \<comment> \<open>Inverses Element\<close>
  and has_inverse: "a \<in> carrier G \<Longrightarrow> inverse G a \<in> carrier G"

definition (in group) is_abelian :: "bool" where
  "is_abelian = (if (\<forall>a \<in> carrier G. \<forall>b \<in> carrier G. mult G a b = mult G b a) then True else False)"


lemma (in group) inv_unique:
  assumes eq: "mult G y x = unit G"  "mult G x y' = unit G"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "y = y'"
proof -
  from G eq have "y = mult G y (mult G x y')" by simp
  also from G have "... = mult G (mult G y x) y'" by (simp add: is_assoc)
  also from G eq have "... = y'" by simp
  finally show ?thesis .
qed

\<comment> \<open>steht nicht im Buch aber ist aus der ersten Implementierung kopiert\<close>



lemma (in group) inv:
  assumes eq: "mult G i a = e G"
and G: "a \<in> carrier G"  "i \<in> carrier G"
shows "i = inverse G a"
proof -
  from G eq have "i \<in> carrier G \<and> mult G i a = unit G" by simp
hence "i = (THE x. x \<in> carrier G \<and> mult G x a = e G)" by (simp add: inv_unique the_equality)

  


(*
lemma g_inv_e:
  assumes eq: "mult G (inverse G a) a = e G"





 "mult G (mult G (inverse G a) a) (inverse G a) = inverse G a"



lemma (in group) inv_r: 
  assumes eq: "mult G i a = e G"
and G: "a \<in> carrier G"  "i \<in> carrier G"
shows "mult G a i = e G"
proof -





lemma groupI:
  fixes G (structure)
  assumes g_closed:
      "\<And>x y. \<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> mult G x y \<in> carrier G"
    and unit_closed: "unit G \<in> carrier G"
    and g_assoc:
      "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> \<Longrightarrow> mult G (mult G x y) z = mult G x (mult G y z)"
    and l_one: "x \<in> carrier G \<Longrightarrow> mult G (unit G) x = x"
    and not_empty: "carrier G \<noteq> {}"
    and has_inverse: "x \<in> carrier G \<Longrightarrow> inverse G x \<in> carrier G"
  shows "group G"
*)



end
