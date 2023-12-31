import Enrichment.Pom.Equiv.Trans

def PomFamilyEquiv {L} [Ticked L] {N}
  (F: PomFamily N L) (G: PomFamily N L)
  := ∀(n: N), PomEquiv (F n) (G n)

def PomFamilyEquiv.refl {L} [Ticked L] {N}
  (F: PomFamily N L)
  : PomFamilyEquiv F F
  := λn => PomEquiv.refl (F n)

def PomFamilyEquiv.symm {L} [Ticked L] {N}
  {F G: PomFamily N L}
  (E: PomFamilyEquiv F G)
  : PomFamilyEquiv G F
  := λn => (E n).symm

noncomputable def PomFamilyEquiv.trans {L} [Ticked L] {N}
  {F G H: PomFamily N L}
  (E: PomFamilyEquiv F G)
  (E': PomFamilyEquiv G H)
  : PomFamilyEquiv F H
  := λn => (E n).trans (E' n)

def PomEquiv.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  (F: PomFamily N L)
  (G: PomFamily N L)
  (E: PomFamilyEquiv F G)
  : PomEquiv (Pom.sigma F) (Pom.sigma G)
  := {
    shared := Pom.sigma (λn => (E n).shared),
    reduce_left := PomReduct.sigma (λn => (E n).reduce_left),
    reduce_right := PomReduct.sigma (λn => (E n).reduce_right),
    iso_left := PomIso.trans 
      (SubPom.sigma_iso (λn => (E n).reduce_left.shared)) 
      (PomIso.sigma (λn => (E n).iso_left)),
    iso_right := PomIso.trans 
      (SubPom.sigma_iso (λn => (E n).reduce_right.shared)) 
      (PomIso.sigma (λn => (E n).iso_right))
  }

def PomFamilyEquiv.toPomEquiv
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: PomFamily N L} {G: PomFamily N L}
  (E: PomFamilyEquiv F G)
  : PomEquiv (F.toPom) (G.toPom)
  := PomEquiv.sigma F G E

def PomEquiv.seq
  {L} [Ticked L]
  {α α': Pom L}
  (Eα: PomEquiv α α')
  {β β': Pom L}
  (Eβ: PomEquiv β β')
  : PomEquiv (α.seq β) (α'.seq β') where
  shared := Pom.sigma (λe: Fin 2 => match e with | 0 => Eα.shared | 1 => Eβ.shared)
  reduce_left := PomReduct.sigma 
    (λe: Fin 2 => match e with | 0 => Eα.reduce_left | 1 => Eβ.reduce_left)
  reduce_right := PomReduct.sigma 
    (λe: Fin 2 => match e with | 0 => Eα.reduce_right | 1 => Eβ.reduce_right)
  iso_left := PomIso.trans 
    (PomReduct.sigma_iso _)
    (PomIso.seq2' _ Eα.iso_left Eβ.iso_left)
  iso_right := PomIso.trans 
    (PomReduct.sigma_iso _)
    (PomIso.seq2' _ Eα.iso_right Eβ.iso_right)

def PomEquiv.par
  {L} [Ticked L]
  {α α': Pom L}
  (Eα: PomEquiv α α')
  {β β': Pom L}
  (Eβ: PomEquiv β β')
  : PomEquiv (α.par β) (α'.par β') where
  shared := Eα.shared.par Eβ.shared
  reduce_left := sorry
  reduce_right := sorry
  iso_left := sorry
  iso_right := sorry