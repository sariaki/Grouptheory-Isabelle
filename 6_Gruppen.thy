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
  \<^enum> eine Verknüpfung "mult", d.h. eine Operation vom Typ carrier \<otimes> carrier \<rightarrow> carrier
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
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
  unit :: "'a" ("e\<index>")

locale group =
  fixes G (structure)
  fixes inverse :: "'a \<Rightarrow> 'a" ("inv")

  assumes not_empty: "carrier G \<noteq> {}"

  and is_closed [intro, simp]: "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<comment> \<open>Zusammensetzungsvorschrift\<close>
    \<Longrightarrow> (a \<otimes> b) \<in> carrier G" 

  and is_assoc: "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<comment> \<open>Assoziativgesetz\<close>
    \<Longrightarrow> (a \<otimes> b) \<otimes> c = a \<otimes> (b \<otimes> c)" \<comment> \<open>Ohne `mult` kriegen wir einen komischen Error\<close>

  and has_identity [intro, simp]: "unit G \<in> carrier G" \<comment> \<open>Einselement\<close>
  and identity_l [simp]: "a \<in> carrier G \<Longrightarrow> e \<otimes> a = a" 

  and has_inverse [intro, simp]: "a \<in> carrier G \<Longrightarrow> inv a \<in> carrier G" \<comment> \<open>Inverses Element\<close>
  and inverse_l [simp]: "a \<in> carrier G  \<Longrightarrow> (inv a) \<otimes> a = e"

begin 
definition is_abelian :: "bool" where
  "is_abelian = (if (\<forall>a \<in> carrier G. \<forall>b \<in> carrier G. a \<otimes> b = b \<otimes> a) then True else False)"

lemma abelian_inv_r:
  assumes abelian: "is_abelian"
  and a: "a \<in> carrier G"
shows "a \<otimes>(inv a) = e"
proof -
  from assms has_inverse inverse_l have "e = (inv a) \<otimes> a" by auto
  also have "... = a \<otimes> (inv a)"
    using abelian is_abelian_def has_inverse a by meson
  ultimately show "... = e" using inverse_l by auto
qed

lemma inverse_r [simp]:
  assumes "a \<in> carrier G"
  shows "a \<otimes>(inv a) = e"
proof -
  have "a \<otimes> (inv a) = e \<otimes> (a \<otimes> (inv a))" using identity_l assms by auto
  also have "... = (inv ((inv a)) \<otimes> (inv a)) \<otimes> a \<otimes> (inv a)" using inverse_l assms by auto
  also have "... = (inv (inv a)) \<otimes> e \<otimes> (inv a)" using assms has_inverse inverse_l is_assoc by metis
  also have "... = (inv (inv a)) \<otimes> (inv a)" 
    using identity_l assms has_identity has_inverse is_assoc by auto
  also have "... = e" using inverse_l assms by auto
  finally show "a \<otimes>(inv a) = e" .
qed

lemma identity_r [simp]: "a \<in> carrier G \<Longrightarrow> a \<otimes> e = a"
proof -
  fix a
  assume 1: "a \<in> carrier G"
  hence "a \<otimes> e = (a \<otimes> (inv a)) \<otimes> a"  
    using has_inverse inverse_l is_assoc by presburger
  also have "\<dots> = e \<otimes> a" using inverse_r is_assoc 1 by auto
  also have "\<dots> = a" using identity_l 1 by auto
  finally show "a \<otimes> e = a" .
qed

text \<open>Postulat 5.\<close>
lemma div_both_1 [simp]:
  assumes "a \<otimes> x = b" 
    and "a \<in> carrier G" "x \<in> carrier G" "b \<in> carrier G"
  shows "x = (inv a) \<otimes> b" using assms
proof -
  from assms have "a \<otimes> x = b" by auto
  hence "(inv a) \<otimes> a \<otimes> x = (inv a) \<otimes> b"
    by (meson assms has_inverse is_assoc)
  hence "e \<otimes> x = (inv a) \<otimes> b" using inverse_l has_inverse assms by auto
  thus "x = (inv a) \<otimes> b" using identity_l has_identity assms by auto
qed

lemma div_both_2 [simp]:
  assumes "y \<otimes> a = b" 
    and "a \<in> carrier G" "y \<in> carrier G" "b \<in> carrier G"
  shows "y = b \<otimes> (inv a)" using assms
proof -
  from assms have "y \<otimes> a = b" by auto
  hence "y \<otimes> a \<otimes> (inv a) = b \<otimes> (inv a)" by auto
  hence "y \<otimes> e = b \<otimes> (inv a)" using inverse_r has_inverse assms is_assoc by auto
  thus "y = b \<otimes> (inv a)" using identity_r assms by auto
qed

text \<open>Postulat 6.\<close>
lemma div_unique [simp]:
  assumes "a \<otimes> x = a \<otimes> x'" 
    and "a \<in> carrier G"  "x \<in> carrier G"  "x' \<in> carrier G"
  shows "x = x'" using assms
proof -
  from assms have "mult G a x = mult G a x'" by auto
  hence "(inv a) \<otimes> a \<otimes> x = (inv a) \<otimes> a \<otimes> x'" 
    using assms has_inverse is_assoc by metis
  hence "e \<otimes> x = e \<otimes> x'" using assms by auto
  then show "x = x'" using assms identity_l by auto
qed

lemma unit_unique:
  assumes "a \<otimes> x = a"
and "a \<in> carrier G" "x \<in> carrier G" 
shows "x = e" using assms
proof -
  have "a \<otimes> e = a" using has_identity assms by auto
  then have "a \<otimes> e = a \<otimes> x" using assms by auto
  hence "(inv a) \<otimes> a \<otimes> e = (inv a) \<otimes> a \<otimes> x"
    using assms div_unique by blast
  hence "((inv a) \<otimes> a) \<otimes> e = ((inv a) \<otimes> a) \<otimes> x" using assms(2) assms(3) is_assoc by simp
  hence "e \<otimes> e = e \<otimes> x" using assms inverse_l by simp
  thus "x = e" using identity_l has_identity assms by auto
qed

lemma inv_unique:
  assumes "x \<otimes> a = e"
and "a \<in> carrier G"  "x \<in> carrier G"
shows " x = inv a" using assms
proof -
  have "x \<otimes> a = e" using assms has_inverse by auto
  hence "x \<otimes> a \<otimes> (inv a) = e \<otimes> (inv a)" using assms has_inverse by simp
  hence "x \<otimes> (a \<otimes>(inv a)) = (inv a)" using assms(2) assms(3) is_assoc by simp
  thus "x = inv a" using assms inverse_r identity_l by simp
qed

lemma one_two_five_implies_three:
  fixes c x e'
  assumes one: "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> (a \<otimes> b) \<in> carrier G"
    and two: "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> mult G (mult G a b) c = mult G a (mult G b c)"
    and five_r: "\<lbrakk>a \<in> carrier G; b \<in> carrier G; mult G a x = b\<rbrakk> \<Longrightarrow> x = (inv a) \<otimes> b"
    and five_l: "\<lbrakk>a \<in> carrier G; b \<in> carrier G; mult G y a = b\<rbrakk> \<Longrightarrow> y = b \<otimes> (inv a)"

    and eq_1: "c \<in> carrier G" "x \<in> carrier G" "e' \<in> carrier G" "a \<in> carrier G"
    and eq: "e' \<otimes> c = c"
    and cx: "c \<otimes> x = a"
  shows "e'\<otimes> a = a"
proof -
  have "c \<otimes> x = a" using cx by simp
  hence "e' \<otimes> a = e' \<otimes> (c \<otimes> x)" by auto
  hence "e' \<otimes> a = (e' \<otimes> c) \<otimes> x"  using cx eq_1 is_assoc by simp
  hence "e' \<otimes> a = c \<otimes> x" using eq by simp
  thus "e' \<otimes> a = a" using cx by simp
qed

lemma help_me:
  assumes "a \<in> carrier G"  "b \<in> carrier G"
  shows "((inv b) \<otimes> (inv a)) \<otimes> (a \<otimes> b) = e"
proof -
  have "((inv b) \<otimes> (inv a)) \<otimes> (a \<otimes> b) = (inv b) \<otimes> ((inv a) \<otimes> a) \<otimes> b" using assms is_assoc has_inverse is_closed by metis
  moreover have "... = (inv b) \<otimes> e \<otimes> b" using assms has_inverse inverse_l by auto
  moreover have "... = (inv b) \<otimes> b" using has_identity identity_r assms by auto
  moreover have "... = e" using assms has_inverse inverse_l by auto
  ultimately show ?thesis by auto
qed

lemma inv_mult:
  fixes a b c
  assumes "a \<in> carrier G"  "b \<in> carrier G" "c \<in> carrier G" "inv(a \<otimes> b) = c"
  shows "inv(a \<otimes> b) = (inv b) \<otimes> (inv a)"
proof -
  from assms has_inverse inverse_l have 1: "c \<otimes> (a \<otimes> b) = e" by auto
  from assms identity_r have "(inv b) \<otimes> (inv a) = ((inv b) \<otimes> (inv a)) \<otimes> e" by auto
  moreover have "... = ((inv b) \<otimes> (inv a)) \<otimes> (a \<otimes> b) \<otimes> (inv (a \<otimes> b))" using has_identity identity_r assms by auto
  moreover have "... = (((inv b) \<otimes> (inv a)) \<otimes> (a \<otimes> b)) \<otimes> (inv (a \<otimes> b))" using has_identity identity_r assms by auto
  moreover have "... = e \<otimes> (inv (a \<otimes> b))" using has_inverse inverse_l assms is_assoc help_me by auto
  moreover have "... = (inv (a \<otimes> b))" using has_identity identity_l assms by auto
  ultimately show ?thesis by auto
qed

(*
fun mult_upto :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where (*\<Pi>v=1..n=?. a*)
  "mult_upto (Suc 0) a = a" |
  "mult_upto 0 a = e" |
  "mult_upto (Suc en) a = a \<otimes> (mult_upto en a)"

definition powr :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "[^]" 75) where 
  "powr a n = mult_upto n a"

lemma mult_upto_helper: 
  fixes a::'a
  fixes n m::nat
  assumes "a \<in> carrier G"
    and "(mult_upto n a) \<in> carrier G"
    and "(mult_upto m a) \<in> carrier G"
  shows "(mult_upto m a) \<otimes> (mult_upto n a) =  mult_upto (m+n) a"
  sorry
*)

(*
lemma powr_addition:
  fixes a::'a
  fixes n m::nat
  assumes "a \<in> carrier G"
    and a: "(a [^] n) \<in> carrier G"
    and "(a [^] m) \<in> carrier G"
  shows "(a [^] n) \<otimes> (a [^] m) = a [^] (n+m)" 
  apply(induction n)
  using powr_def assms apply(auto)
  apply(simp add: mult_upto_helper)
  done
*)
  
(*
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