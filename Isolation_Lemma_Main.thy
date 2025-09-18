theory Isolation_Lemma_Main
  imports Isolation_Lemma_Defs
begin

lemma exist_minimizer:
(*prove that for a set family F there must exist at least one minimier
  1. prove that for an element S in F, there is natural number n to be the wt of S
  2. take the smallest n, namely m, and the according set A
  3. prove m is smaller or equal to other n*)
  assumes "F \<noteq> {}"
  obtains A where "A\<in>F" "minimizer F w A"
proof-
  obtain S0 where "S0 \<in> F" using assms by auto
  have sum: "\<exists>n::nat. \<exists>S\<in>F. wt w S = n" (*non-empty*)
  proof- 
    have "\<exists>S\<in>F. wt w S = wt w S0" 
      using \<open>S0 \<in> F\<close> by auto
    then show ?thesis by auto
  qed

  define m::nat where "m = (LEAST n. \<exists>S\<in>F. wt w S = n)"
  from sum have "\<exists>S\<in>F. wt w S = m"
    unfolding m_def by (rule LeastI_ex)
  then obtain A where "A\<in>F" and Awt: "wt w A = m" by auto

  have "\<forall>B\<in>F. wt w A \<le> wt w B"
  proof
    fix B assume "B\<in>F"
    have "\<exists>S\<in>F. wt w S = wt w B"
      using \<open>B\<in>F\<close> by auto
    hence "m \<le> wt w B" 
      unfolding m_def by (rule Least_le)
    thus "wt w A \<le> wt w B"
      using Awt by simp
  qed

  then show ?thesis using \<open>A\<in>F\<close> that
    unfolding minimizer_def by blast
qed


lemma no_unique_minimizer :
  (*From exist_minimizer, there must exist at least one minimizer
    then since we assume it is not unique, there must be at least two.*)
  assumes "F \<noteq> {}" "\<not>has_unique_minimizer F w"
  obtains A B where "minimizer F w A" "minimizer F w B " "A \<noteq> B" "A \<in> F" "B \<in> F"
proof - 
  obtain A where A: "A\<in>F" "minimizer F w A"
    using exist_minimizer [OF assms(1)] by auto

  obtain B where B: "B \<in> F" "minimizer F w B" "B \<noteq> A" 
    using assms(2) A unfolding has_unique_minimizer_def 
    by auto
  show ?thesis
    using A B that by blast
qed

lemma two_minimizers_not_unique:
  (*Assume two different minimizers A and B in F,
    if the uniqueness holds, A and B must be equal,
    thus contradicts with our assumption that A \<noteq> B*)
  assumes  "minimizer F w A" "minimizer F w B " "A \<noteq> B" "A \<in> F" "B \<in> F"
  shows "\<not>has_unique_minimizer F w"
proof
  assume "has_unique_minimizer F w"
  then obtain X where X: "X\<in>F \<and> minimizer F w X"
    and unique: "\<forall>Y. Y\<in>F \<and> minimizer F w Y \<longrightarrow> Y = X"
    unfolding has_unique_minimizer_def by auto
  from unique \<open>A \<in> F\<close> \<open>minimizer F w A\<close> have "A = X" by auto
  from unique \<open>B \<in> F\<close> \<open>minimizer F w B\<close> have "B = X" by auto
  hence "A = B" using \<open>A = X\<close> \<open>B = X\<close> by simp
  with assms(3) show False by simp
qed

lemma not_unique_iff_exist_two:
  assumes "F \<noteq> {}"
  shows "\<not> has_unique_minimizer F w
         \<longleftrightarrow> (\<exists>A B. A \<in> F \<and> B \<in> F \<and> minimizer F w A \<and> minimizer F w B \<and> A \<noteq> B)"
  by (metis assms no_unique_minimizer two_minimizers_not_unique)


lemma minimizers_same_weight:
(* If A and B are both minimizers, then their weights must be equal. *)
  assumes "minimizer F w A" "minimizer F w B"
  shows "wt w A = wt w B"
  using assms unfolding minimizer_def by (meson order_antisym le_cases order_trans)


definition alpha :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> nat" where
(* Definition of alpha: it measures the difference between
   the minimal weight of sets not containing x
   and the minimal residual weight of sets containing x. *)
  "alpha w F x =
     (LEAST n. \<exists>S\<in>F. x \<notin> S \<and> wt w S = n)
   - (LEAST n. \<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = n)"

lemma minimizer_B_eq_least_not_in:
(* If B is a minimizer and x \<notin> B,
   then the least weight among sets not containing x must be realized by B,
   i.e. equals wt w B.
   This eliminates the first LEAST in the definition of alpha. *)
  assumes "minimizer F w B" "x \<notin> B"
  shows "(LEAST n. \<exists>S\<in>F. x \<notin> S \<and> wt w S = n) = wt w B"
proof -
  have B_inF: "B \<in> F" and B_le: "\<forall>S\<in>F. wt w B \<le> wt w S"
    using assms(1) unfolding minimizer_def by auto
  have witness: "\<exists>S\<in>F. x \<notin> S \<and> wt w S = wt w B"
    using B_inF assms(2) by auto
  have least: "\<And>n. (\<exists>S\<in>F. x \<notin> S \<and> wt w S = n) \<Longrightarrow> wt w B \<le> n"
  proof - 
    fix n assume "\<exists>S\<in>F. x \<notin> S \<and> wt w S = n"
    then obtain S where "S\<in>F" "x\<notin>S" "wt w S = n" by auto
    hence "wt w B \<le> wt w S" using B_le by auto
    thus "wt w B \<le> n" using \<open>wt w S = n\<close> by auto
  qed

show ?thesis
  by (smt (verit) B_le Least_equality witness) 
qed

lemma wt_split_point:
(* Splitting formula: if x \<in> S, then
   wt w S = wt w (S - {x}) + w x. 
   Quite simple lemma for brevity in following proof *)
  assumes "finite S" "x \<in> S"
  shows "wt w S = wt w (S - {x}) + w x"
  using assms unfolding wt_def by (simp add: sum.remove)

lemma minimizer_A_eq_least_in_residual:
(* If A is a minimizer and x \<in> A,
   then the least residual weight among sets containing x
   is realized by A−{x}, i.e. equals wt w (A−{x}).
   This eliminates the second LEAST in the definition of alpha. *)
  assumes "finite U" "F \<subseteq> Pow U" "minimizer F w A" "x \<in> A"
  shows "(LEAST n. \<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = n) = wt w (A - {x})"
proof -
  have A_inF: "A \<in> F" and A_le: "\<forall>S\<in>F. wt w A \<le> wt w S"
    using assms(3) unfolding minimizer_def by auto
  have AU: "A \<subseteq> U" using A_inF assms(2) by auto
  have finA: "finite A" using AU assms(1) finite_subset by auto
  have witness: "\<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = wt w (A - {x})"
    using A_inF assms(4) by auto

  have least: "\<And>n. (\<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = n) \<Longrightarrow> wt w (A - {x}) \<le> n"
  proof - 
    fix n assume "\<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = n"
    then obtain S where Sin: "S\<in>F" and xin: "x\<in>S" and Sres: "wt w (S - {x}) = n" by auto

    have SU: "S \<subseteq> U" using Sin assms(2) by auto
    have finS: "finite S" using SU assms(1) finite_subset by auto
    have "wt w A \<le> wt w S" using A_le Sin by blast
    hence "wt w (A - {x}) + w x \<le> wt w (S - {x}) + w x"
      using wt_split_point[OF finA assms(4)] wt_split_point[OF finS xin] by simp
    thus "wt w (A - {x}) \<le> n" using Sres by simp
  qed
  show ?thesis by (smt (verit, del_insts) LeastI2_wellorder_ex Least_le least order_antisym_conv witness)
qed


lemma two_minimizers_alpha_eq:
(* Main conclusion:
   If A and B are two distinct minimizers and x \<in> A−B,
   then alpha w F x = w x.
   We use the lemma proved above to connect the two "LEAST"s *)
  assumes "finite U" "F \<subseteq> Pow U"
          "A \<in> F" "B \<in> F"
          "minimizer F w A" "minimizer F w B"
          "A \<noteq> B" "x \<in> A - B"
  shows   "alpha w F x = w x"
proof -
  have x_in: "x\<in>A" and x_out: "x\<notin>B" using assms(8) by auto
  have Least_out: "(LEAST n. \<exists>S\<in>F. x \<notin> S \<and> wt w S = n) = wt w B"
    by (simp add: assms(6) minimizer_B_eq_least_not_in x_out)
  have Least_in: "(LEAST n. \<exists>S\<in>F. x \<in> S \<and> wt w (S - {x}) = n) = wt w (A - {x})"
    using assms(1,2,5) minimizer_A_eq_least_in_residual x_in
    by fastforce


  have eqAB: "wt w A = wt w B"
    using assms(5,6) minimizers_same_weight by auto

  have finA: "finite A" using assms(1,2,3)
    by (meson Pow_iff rev_finite_subset subset_iff)
  have splitA: "wt w A = wt w (A - {x}) + w x"
    by (simp add: finA wt_split_point x_in)

  show ?thesis 
  by (metis (mono_tags, lifting) Least_in Least_out
      add_diff_cancel_left' alpha_def eqAB
      splitA)
qed




theorem isolation_lemma_main :
  fixes U :: "'a set" and F :: "'a set set" and N :: nat
  assumes "finite U" "F \<subseteq> Pow U" " F \<noteq> {}" "N \<ge> 1"
  shows
    "measure_pmf.prob (w_pmf N U){w. has_unique_minimizer F w} \<ge> 1 - real(card U)/real N"
proof-
  (*bad case:(at least) two sets have same weight, suppose A and B
    can find a point x where x \<in> A but x \<notin> B.
    define \<alpha>(x) according to the proofs, then if "bad",
    \<alpha>(x) = w(x), which is at most 1/N;
    so for the probability that such x exists is at most n*1/N
    *)

qed

end