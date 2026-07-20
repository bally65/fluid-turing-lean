# Navier–Stokes existence/smoothness formalization roadmap

日期：2026-07-20

## 0. 結論先行

目前兩個 repository **都沒有證明或形式化三維 Navier–Stokes 全域存在性與光滑性**。

- `fluid_turing_lean` 的主成果是連續流與光滑離散映射的 reachability 不可判定性。
  M7/M61 是可退化滿足的抽象 signature，適合做規格與假設帳本，不是真 PDE 語義。
- `contact_geometry_lean` 已有平坦 `ℝ³` 的 `grad`、`divergence`、`convDeriv`、
  `vectorLaplacian` 等真算子。C141–C219 已給出一個具體時變解、非空洞的 forward-IVP
  規格、該顯式 mode 在緊緻 `T³` 上的有限 Haar 能量律、scalar/vector Fourier–Parseval、
  拉回後的一二階 multiplier，以及有限支撐複向量場的實值條件、散度、Leray、Stokes、
  pressure、精確對流能量抵消，以及 fixed-cutoff ODE 的局部存在／解芽唯一性、無散度軌道
  不變、實值解芽不變、精確 pointwise energy derivative，以及 `ν≥0` 時同一局部區間上的
  energy monotonicity／forward initial bound，以及每個 compact interior time interval 上的
  exact coefficient energy-dissipation balance、由 coefficient energy 控制 actual
  ODE-carrier norm 的 forward bound、bounded state ball 上統一的正 local restart step，以及
  common compact interval 上的 whole-interval uniqueness/reality，以及**原始 fixed-cutoff
  Galerkin ODE 從任意初始時間出發的 unique forward-global admissible solution**與所有 forward
  compact intervals 的 exact integrated coefficient energy balance。C172 另建立 nested symmetric
  frequency cubes 與同一 real vector `L²(T³)` datum 的相容 Fourier projections。C173–C175 現已
  證明 real `L²` Fourier conjugate symmetry、finite Leray 的精確 Pythagorean energy contraction，
  並對任意 real vector `L²` datum 自動產生 restriction-coherent、real、transverse 的
  cube initial states。C176 再對 `ν>0` 給出數值不含 cube radius 的
  `∫D_N ≤ E_L²/(2ν)` 時間積分耗散界。C177 證明 canonical cubes exhaustive/cofinal，
  raw initial energies 趨向完整 Parseval energy；Leray-projected cube energies則趨向一個
  summable projected coefficient total，actual complementary tails 趨零，且該 total 僅保證
  `≤ E_L²`（already-transverse data 才有 equality）。C178 將每個 finite coefficient state
  重建到同一個 quotient-torus complex `L²` carrier；C179 證明 `i n_j` multiplier fields 的
  pullback 是實際 Euclidean coordinate derivatives，且三方向 `L²` energy 精確等於 `D_N`；
  C180 因而把 C176 改寫成 field-level exact energy/gradient balance，並在 `ν>0` 得到
  `∫‖∇u_N‖²≤E_L²/(2ν)`。這是 finite-Fourier homogeneous gradient seminorm，不是 completed
  `H¹`。C181 以一次 dependent choice 將每個 cube 的同一組初值、ODE、能量、梯度與唯一性
  證書包成 `N ↦ U_N` 的 common-carrier family，但不宣稱不同 `N` 相容。C182 將 finite
  reconstruction 綁成 continuous linear map，因而證明每個 selected `U_N` 在 `Ici t₀` 上
  time-continuous。C183–C184 建立各向同性 `(1+|n|²)⁻³` 可加權重及一個真正完備、所有
  cutoffs 共用的 weighted Fourier coefficient carrier；C185–C186 再先逐 output mode、後對
  retained support 求和，得到不含 cutoff cardinality 的
  `E_H⁻³(PB_N(c,c)) ≤ C₋₃ E(c)D(c)`。C187 再證 Stokes bound 並得到完整 static RHS
  estimate `E_H⁻³(RHS_N(c))≤2ν²E(c)+2C₋₃E(c)D(c)`。C188 將 actual Galerkin ODE derivative
  輸送到共同 carrier；C189 將該平方能量沿 forward compact intervals 真正積分，得到
  `∫E_H⁻³(RHS_N)≤2ν²E₀(b-a)+(C₋₃/ν)E₀²`；C190 證明 RHS 的 Bochner integrability 與 exact
  FTC；C191 得到 cutoff-independent squared increment estimate
  `‖U_N(b)-U_N(a)‖²≤(b-a)(2ν²E₀(b-a)+(C₋₃/ν)E₀²)`。C192 再取平方根、對稱化 endpoints，
  以同一顯式 modulus 證整族在 whole forward ray 上的 `UniformEquicontinuousOn` 與
  `EquicontinuousOn`。C193 證 `(M+1)²‖U_N-P_MU_N‖²≤D_N` 與
  `∫‖U_N-P_MU_N‖²≤E₀/(2ν(M+1)²)`；C194 將 C192 經固定低模態 recovery CLM 搬到
  common field `L²`，對每個 fixed `M` 得整族 `P_MU_N` 的 uniform equicontinuity。C195 再證
  同時具有 pointwise energy/dissipation bounds 的 finite-Fourier field sublevel totally bounded，
  且其 common-`L²` closure compact。C196 對每個 fixed `M` 以有限維 compact range 與 C194
  equicontinuity 套用 Arzelà--Ascoli，得到 compact-time uniform path closure；C197 把它連續送入
  明示的 iterated Bochner carrier `Lp_t(CurrentT3ComplexVectorL2)`。在 `ν>0` 時，C198 證此 carrier 中
  full/low 差的平方範數等於 C193 的 interval integral，因而對每個 `t₀≤a≤b` 證 full Galerkin
  family totally bounded、closure compact，並抽出 `StrictMono` cutoff subsequence 強收斂。
  C199 再把所有 integer exhaustion windows 的 compact closures 組成 countable
  product，一次抽同一 `StrictMono` subsequence 在每個 `[t₀,t₀+m]` 收斂。C200 構造 nested-window
  norm-nonincreasing `Lp` restriction CLM，證 actual fields commute，並由 limit uniqueness 得
  `m≤n` 時 `restrict (U n)=U m`。C201 把 compatibility 封裝成 complex submodule，將每個
  actual cutoff 與共同 subsequence limit 都放入 projective-limit-style `L²_loc` carrier，並把
  windowwise convergence 升級成該 subtype 的 `Tendsto`。C202 再把三個 spatial coordinate
  projections 提升到 outer time `L²`，對任意 quotient class 證
  `‖F‖²≤Σᵢ‖Fᵢ‖²≤3‖F‖²`，且中項精確等於 integrated displayed vector energy。
  C203 進一步證 arbitrary-filter local convergence 等價於所有 window/scalar coordinates 的
  convergence，並將 coordinate extraction 核證為 injective topological embedding；在 `ν>0`
  時，C201 的同一 `U` 與同一 `StrictMono` subsequence 也同步收斂到 bundled-coordinate image。
  C204 再以 spatial 與 outer-time 兩層 Hölder 建立明示的 iterated `L¹_t(L¹_x)` multiplication，
  對任意 filter 證九個 ordered coordinate products 的 bundled `(m,i,j)` convergence；在 `ν>0`
  時，沿用 C203 的同一 `U` 與同一 `φ`，沒有重抽 subsequence。C205 接著構造 generic
  norm-nonincreasing outer-`Lp` restriction，證 identity／transitivity、coordinate extraction 與
  two-level products 都和 nested-window restriction commute，將 compatible `(m,i,j)` systems
  封裝成 projective-limit-style product `L¹_loc` submodule，並把同一 `U,φ` 的 product
  convergence 升進 subtype topology。C206 再以兩層 `L∞×L¹` pairing，對 nested bounded-
  continuous tests 建立 literal space-then-time integral、unit-constant norm bound 與 exact-one
  nonzero witness；每個固定 `(m,i,j,Ψ)` 都把 C205 compatible-carrier convergence 連續送成
  scalar convergence，仍沿用同一 `U,φ`。C207 再把 C179 的 finite-Fourier coordinate
  multiplier derivatives 封裝成 bounded-continuous spatial tests，核證 exact cover derivative
  與非零 transverse witness，加入 bounded-continuous time envelope，並把九個 C206 pairings
  組成具有 componentwise norm bound 與 unit-tensor nonzero witness 的 generic tensor CLM。其
  finite-Fourier specialization 給出 unsigned
  `ΣᵢΣⱼ∫ₜ∫ₓ η(t) ∂ⱼϕᵢ(x) Pᵢⱼ(t,x)` 的 literal nested formula，以及 arbitrary-filter／同一
  `U,φ` 的 scalar convergence；尚未另證 specialized functional 非零。C208 接著對兩個不同
  finite coefficient families 證 Hermitian cross-Parseval 與 cross-gradient Parseval，把 literal
  normalized-Haar integrals 精確辨識為 common-cutoff coefficient pairings，並證 Stokes cross
  pairing 是 `-ν` 乘 weighted cross sum；兩個不相等的 explicit complex families 使兩種 cross
  sums 都精確等於 `Complex.I`。C209 再證 transported monomial product、single/triple
  normalized-Haar selection laws、三族 finite fields 的 literal product-gradient component
  expansion，以及 test mode `r` 對 convection output `-r` 的 reflected coefficient expansion。
  C210 用 state transversality、`p↔q` reindex與 zero-sum relation把兩者接成 exact global-minus
  identity，再以 test transversality移除 reflected Leray projector並組出 static Galerkin RHS；
  symmetric-cutoff admissible witness使 RHS pairing精確為 `-Complex.I`。C211 再沿 actual
  fixed-cutoff Galerkin trajectory加入 differentiable scalar time envelope、product rule、explicit
  endpoints與 FTC，得到 `∫(-η'G+νηD-ηQ)=η(a)G(a)-η(b)G(b)`；C171 actual curve與 C181 stored
  family 都有 ordered-interval及 `compactIntervalVolume`版本。C212 再把 linear time/viscous
  terms封裝為 local velocity `L²` carrier上的 CLM，精確辨識 C207 product functional為 `∫ηQ`，
  並沿 C205 同一 `StrictMono` velocity/product subsequence取極限；final envelope為零時，右端是
  ambient initial datum的 reflected Fourier pairing，不評估 limit `L²` class的 endpoint。C213 再
  封裝 admissible separated tests及其 finite CLM sums，證 literal iterated-integral、同一 cutoff、
  同一 subsequence與同一 selected `U,phi` 的 finite-family identities。C214 將逐項
  final-zero放寬成 literal aggregate final coefficient cancellation；C215 在每個正長整數
  window 內構造共用、非平凡、support 嚴格落在 interior 的 smooth compact time bump。
  C216 把弱殘差分解成 velocity CLM、product CLM、已評估 initial scalar 與 terminal
  coefficient 四個 algebraic slots，並用 unit-initial formal jet 證明 ambient zero-final kernel
  並非全被殘差消去。C217 只對所有 literal realizable zero-final jets 取
  `Submodule.span`，證明這個有限代數 span 落在同一 selected residual kernel。C218 分開
  complex-linear transversality 與僅 real-linear 的 conjugate-symmetry reality，封裝其交集、
  Leray wrappers、非零 witness 與 C215 consumer。C219 把 zero-final jet 投影到三個
  consumer slots，在 CLM slots 的 bounded-convergence topology 上將 fixed-`U,P` residual 證成
  continuous linear map；projected realizable span 的 closure 落在其 closed kernel，但
  unit-initial consumer 以殘差 `-1` 把它與 whole ambient consumer 分離。這只否定
  **whole ambient consumer 的 naive density**；正確下一目標是 residual kernel 內的
  closure/density，或先建立 intrinsic physical test carrier 再證對應 density。現在已有 compatible local
  quotient classes 的正式載體、finite-window squared-norm bridge、faithful scalar-coordinate
  topology bridge、coordinate-product convergence 與 outer-time cross-window compatibility；尚未完成
  global representative、canonical joint-product Euclidean-vector carrier、
  physical/global representation、一般 smooth-test density、pointwise initial trace、limiting energy
  inequality與標準 Leray--Hopf torus弱解；flat NS
  field-level 解本身也仍只處理一個特殊初值。

因此目前工程里程碑是 **L1.26：finite-cutoff core、`ν>0` 時同一 cutoff subsequence 在 whole
integer exhaustion 上的 compatible local strong limits、finite-window squared-norm bridge、
faithful scalar-coordinate embedding，以及全部九個 coordinate products 在明示 iterated
`L¹_t(L¹_x)` carriers 中的 strong convergence，以 outer-time restriction identities 跨視窗
相容、封裝進 projective-limit-style product `L¹_loc` subtype，且每個固定 nested
bounded-continuous test pairing 與 finite-Fourier quadratic-gradient tensor pairing 收斂，且
finite-Fourier Hermitian cross-Parseval／cross-gradient／Stokes duality、triple-monomial
selection、signed complex-bilinear reflected convection、static Galerkin RHS、fixed-cutoff
spacetime identity、同一 subsequence 上的 separated finite-Fourier limiting weak identity，及其
finite presentation sums、aggregate endpoint cancellation、common compact-time bump、realizable residual-jet
algebraic span、transverse/reality carriers，以及 whole ambient consumer naive-density 的拒絕 gate
已核證**。
C165–C171 完成 compact-support globalization、de-truncation、time shift 與 uniqueness；C172 完成
nested initial projections 與共同 `L²` bound；C173–C175 把 arbitrary real `L²` datum 自動接到
real/transverse Leray-projected cube states；C176 完成第一條 cube-independent integrated
coefficient-dissipation bound；C177 完成 initial coefficient-energy exhaustion/tail limit。
C178–C182 再完成 finite fields 的共同 `L²` reconstruction、實際 cover derivatives、精確
homogeneous-gradient identity、field-level spacetime bound、cutoff-indexed selection 與逐 cutoff
common-carrier time continuity；C183–C259 已完成 summable `H⁻³` weight、complete coefficient
carrier、cutoff-independent full RHS bound、actual trajectory derivative transport、time-integrated
squared RHS-energy bound、Banach FTC、squared time-increment estimate 與 whole-forward-ray
uniform equicontinuity，加上 integrated Fourier-tail、fixed-low-mode common-`L²` equicontinuity、
static Fourier--Rellich closure、compact-time low-mode Ascoli、iterated spacetime carrier、
fixed-window compactness、countable exhaustion diagonalization、nested-window limit
compatibility、projective-limit-style local carrier、三座標 spacetime squared-norm 的定量等價、
所有 window/scalar coordinates 對 local topology 的 faithful embedding、two-level Hölder、
九個 ordered coordinate products 的 arbitrary-filter iterated-`L¹` convergence，以及 scalar
outer-`L¹` restriction compatibility、product `L¹_loc` carrier、bounded-continuous iterated test
pairings，以及 finite-Fourier spatial derivatives 所生成的九項 unsigned quadratic-gradient
functional、兩族 finite-Fourier fields 的 Hermitian cross-Parseval／cross-gradient／Stokes
duality、triple monomial selection、physical/reflected coefficient signed identity、transverse-test
Leray removal、static Galerkin RHS、fixed-cutoff time-envelope／endpoint／FTC identity，以及
C212 的 limiting finite-Fourier carrier identity、C213 finite-family CLM sums、C214 aggregate
endpoint cancellation、C215 common compact-time bump、C216–C217 residual-jet/span 代數封裝、
C218 transverse/reality carriers、C219 bounded-convergence consumer closure gate，以及 C220
residual-kernel product-moment strict obstruction。C221–C227 再建立 mathlib `𝓓(ℝ,ℂ)` canonical
LF smooth compact time-test carrier、closed zero-final kernel、window/derivative maps、separated-test
bridge、三個 time-linear residual slots、literal realizable-span provenance與 finite-family weak
identities。C228 將 reflected initial pairing封裝成 spatial `LinearMap`，C229 先以 algebraic
`TensorProduct.lift` 因子化 initial slot；C230–C232 再證 velocity、product-gradient與完整三槽
consumer 的 spatial complex-linearity，C233 將完整 consumer提升到同一 algebraic tensor。
C234 以 tensor induction把 whole range放入 realizable span並得到同一 selected `U,φ` 上的
residual vanishing；C235 命名 exact image，證其 closure obeys必要的 product-moment與 selected
residual-kernel constraints。C236–C238 建立固定視窗 exact-kernel quotient與 residual
factorization；C239–C243 加入 integer-window coverage、finite-support all-window DirectSum、exact
global image與 strict-tail `η,η'` vanishing；C244–C245 再建立 global faithful quotient及 residual
factorization。C246 給出 nested compact-window zero-extension integral transport，C247 首次把它
接到 C223，證 sufficiently late windows 上完整 velocity/viscous consumer穩定；C248 把同一
stability 推到 product-gradient slot，C249 再合併 initial slot與完整三槽 consumer。C250 命名
canonical stabilized consumer value；C251–C252 分別建立 global-time 與 spatial linearity，C253
把它們封裝成 window-free bilinear map及 global algebraic tensor lift。C254–C255 證 whole range
realizable、selected residual為零，並刻畫必要 closed constraints；C256–C258 建立 faithful kernel
quotient及 selected residual經 image／quotient 的 factorization；C259 證 global stabilized image
包含於舊 finite-support all-window image。C260 將此單向 inclusion 封裝為 exact-image embedding，
C261 再得到 global faithful quotient到 all-window faithful quotient的單向 injective algebraic map，
C262 證兩邊 scalar residual的 naturality。這仍沒有 reverse inclusion、surjectivity、image equality、
quotient equivalence或新 residual vanishing theorem。
C263–C266 另建立 second-order weighted-`lp 1` coefficient carrier、closed complete transverse
coefficient subtype、absolutely convergent continuous-torus synthesis與 contractive normalized
coefficient multipliers；C267 將 transverse coefficients放入 mathlib canonical LF time-test carrier，
但沒有宣稱該 LF carrier是 `CompleteSpace`，也沒有 coefficient reality。C268 建 algebraic
separated tensor lift，C269 將 zeroth-order synthesis封裝成 continuous linear map，C270 逐時
postcompose成 continuous-field-valued LF tests，C271 再記錄 algebraic tensor composite的 pure-tensor
pointwise公式與 explicit nonzero continuous-field witness。該 witness 尚未證為 composite range中的像；
continuous field也未辨識為 intrinsic smooth或 divergence-free field，並且沒有 density theorem。
C272–C275 接著建立 real-linear conjugate reflection、closed coefficient-reality與 real-transverse
intersection，以及 finite real-transverse families 的 injective embedding。C276–C279 證 reality
經 continuous synthesis與 normalized coordinate/frequency-square symbols保存，並將 diagonal
coordinate-symbol sum辨認為 `I * fourierWaveDot`、故在 transverse coefficients上為零；這仍只是
coefficient-symbol cancellation，不是 intrinsic derivative、Laplacian或 divergence theorem。
C280 建 real-transverse coefficient-valued LF carrier；因 pinned typeclass/API direct route blocker，
C281 改用等距同構的 native target `C(T3, Fin 3 → ℝ)`，C282 建 native-real LF transport與
time-derivative commutation，C283 再給 explicit nonzero zero-mode witness，且只證這一個 witness
位於 C282 zero-final transport range。這不修補 C271 的不同 tensor-composite range gap。
在 `ν>0` 的 actual-family theorem 中，前述速度、乘積、C207 pairings與 weak identity沿用同一
`U,φ`。歷史 C247 checkpoint 的 contact code/receipt 為 `612e758`／`92e2a97`，當時的
5126-declaration axiom gate與 244/244 consistency 均通過；歷史 C259 checkpoint 為
`8e89a6c`／`019842c`；歷史 C271 checkpoint 為 `d62ff30`／`8a7dfd5`。
**目前 C283 checkpoint 已完成：contact code
`9b08bef28a6849ae53e2381e3ab45001a00f281b` 與 receipt
`ff7030b9169114dfa928c8ef5f84d8c14ce9e479`；280 modules、3796 source declarations、
5943 audited declarations、280/280 consistency、8861-job full build、zero-sorry及
standard-three-axiom gate均通過。**下一個低成本 gate 是把已驗證的 real coefficient-symbol
maps逐步接到正確的 LF／physical-test interface；LF completeness、intrinsic divergence、
completed physical-test topology與 representation仍需各自證明。
任何 density目標都必須放在正確 image或 residual-compatible target；其後才是 weak gradient、
initial trace與一般 test-space PDE limit。

## 0.1 距離評估：不能用單一百分比

「離完成多遠」必須拆成四種不同距離；把它們混成一個百分比會嚴重誤導：

| 距離層 | 現在位置 | 還缺什麼 | 誠實判定 |
| --- | --- | --- | --- |
| 固定 cutoff Galerkin / compactness gate | C153–C283 已完成 fixed-cutoff global core、共同 field reconstruction 與 uniform estimates；在 `ν>0` 時，一條 `StrictMono` cutoff subsequence 在每個 `[t₀,t₀+m]` 強收斂，local quotient limits 與所有 coordinate products 沿同一 subsequence收斂；fixed/limiting finite-Fourier identities、canonical LF zero-final tests、realizable residual span、finite-family identities、ambient/residual-kernel obstruction、complete algebraic tensor consumer/image、fixed/global faithful quotients、全部三槽的 sufficiently-late window stability、window-free global algebraic tensor、exact realizable image、單向 quotient/residual naturality、weighted-`lp 1` coefficient reality／real transversality，以及 native-real LF transport亦完成 | LF completeness、intrinsic/completed physical-test topology、intrinsic tangent-field/divergence identification、正確 density/closure theorem、physical representation、weak gradient、pointwise initial trace與 standard PDE identification；C260–C262 仍沒有 reverse inclusion/equality，C271 witness仍無 tensor-composite range證明，C283只處理不同 transport map的一個 witness | **whole ambient consumer 與 whole residual kernel 都已證過大；尚非一般 test-space weak solution** |
| 已知週期 3D NS 理論 | Fourier/Parseval/Galerkin、energy/gradient bounds、negative-space time control、compatible local strong limits、coordinate/product carriers、finite-Fourier cutoff-limit identities、canonical LF time tests、finite smooth-test weak identities、全部 consumer slots 的 cross-window stability、window-free global algebraic tensor、exact realizable image、faithful quotient、residual naturality、weighted-coefficient reality與 native-real continuous/LF synthesis已有 | LF `CompleteSpace`、intrinsic/completed Sobolev與 physical-test carrier、intrinsic divergence、canonical physical joint-product representation、global representative、weak gradient、adequate smooth-test weak formulation、pointwise initial trace、energy inequality、Leray–Hopf、local strong、weak–strong uniqueness、條件正則性 | **仍很遠；C220–C283 建立了穩定 algebraic quotient/factorization與 real coefficient-to-coordinate-field bridge，但沒有 physical-test density 或 weak solution** |
| Clay 問題的正式陳述 | 可精確區分 global regularity 與 finite-time breakdown | 函數空間、初值類別、maximal solution 與 breakdown alternative 的完整介面 | **可形式化，但只是把問題說清楚** |
| Clay 未解核心 | 尚無 theorem | 對任意大光滑 divergence-free 3D 初值證永遠光滑，或構造合格 finite-time singularity | **距離未知、不可估工期；C283 不改變此判定**；需要新數學，不是多蓋幾磚必然到達 |

所以「完成已知有限維 Galerkin existence/uniqueness 核心」已由 C168–C171 達成，
C172–C177 又完成 arbitrary real `L²` 的 admissible initial-data bridge、第一條共同積分耗散界，
以及 exhaustive cubes 上的 initial coefficient-energy/tail convergence；在 `ν>0` 的 actual
compactness/subsequence conclusions 下，C178–C283 已把這些
量放進共同 finite-field/negative coefficient carriers、得到 field-level homogeneous-gradient
spacetime bound，並完成 cutoff-indexed choice、actual negative-space derivative、time integral、
Banach FTC、uniform squared increment estimate、forward equicontinuity、integrated Fourier tail、
fixed-low-mode field equicontinuity、static closure、fixed-window compactness，以及 whole
integer exhaustion 上的 compatible local strong limits、projective carrier、coordinate-energy
norm comparison、scalar-coordinate topological embedding，以及 iterated-`L¹` coordinate-product
convergence／cross-window compatibility／product `L¹_loc` carrier、fixed-test scalar pairing，
以及 finite-Fourier quadratic-gradient pairing convergence，再補 Hermitian cross-duality、
triple-monomial selection、signed physical/coefficient convection、Leray removal、static RHS與
fixed-cutoff spacetime weak identity，並沿同一 subsequence得到 limiting finite-Fourier carrier
identity、finite sums、aggregate endpoint cancellation、common compact-time bump、realizable
residual-jet span、transverse/reality carriers，並以 C219–C220 定位 whole ambient consumer
與 whole residual kernel 都過大的反例；C221–C259 再接上 canonical LF zero-final time tests、
finite-family weak identities、complete algebraic tensor consumer、faithful fixed/global quotients、
all-window image factorization、tail vanishing、zero-extension integral、全部三槽的 window stability、
canonical window-free global tensor、exact realizable image、faithful quotient、selected residual
factorization與 C259 的單向 global-image inclusion。C260–C262 把該 inclusion 搬到 faithful
quotients並證 residual naturality，但仍只有單向 algebraic embedding。C263–C271 再建立
weighted-`lp 1` transverse coefficient subtype、absolute synthesis、LF coefficient／continuous-field
tests與 separated pure-tensor pointwise bridge；C272–C283 補 coefficient reality、real-transverse
intersection、reality-preserving symbols、native-real coordinate fields與 LF transport。仍沒有 LF
completeness、intrinsic tangent-field/divergence identification或 density；C271 的 explicit witness
仍未證在 tensor-composite range，C283只證另一 transport map的一個 displayed range member。
歷史 C247 contact checkpoint 為 `612e758`／`92e2a97`，歷史 C259 checkpoint為
`8e89a6c`／`019842c`，歷史 C271 checkpoint為 `d62ff30`／`8a7dfd5`；
**目前 C283 contact checkpoint為
`9b08bef28a6849ae53e2381e3ab45001a00f281b`／
`ff7030b9169114dfa928c8ef5f84d8c14ce9e479`，280 modules、3796 source declarations、
5943 audited declarations及 280/280 consistency receipts如上。**其後才處理 LF與
intrinsic/completed physical-test結構、正確 density/closure、足夠的 physical representation
與已知弱解理論基建。
不能承諾的
是由目前進度外推 Clay 終局。

若只把 **NS040 finite-Galerkin fixed-cutoff core** 當作軟體 ticket，現在可標記為
**100% complete**：ODE、constraints、global existence/uniqueness、energy laws、arbitrary-real-data
Leray launch 與第一層 common bounds 已全部入庫。這個 100% 只屬於限定後的工程包；
**在 `ν>0` 的 actual compactness/subsequence conclusions 下，C178–C283 已完成 NS050/NS070
前的 finite-field spatial/selection bridge、negative-carrier
trajectory derivative、integrated RHS estimate、FTC、uniform equicontinuity、integrated high
tail、fixed-low-mode compact paths、iterated carrier、fixed-window compactness、exhaustion
diagonalization、local-limit projective carrier、finite-window coordinate norm bridge與
scalar-coordinate topological embedding、compatible iterated coordinate-product carrier、
fixed-test scalar pairing、finite-Fourier quadratic-gradient functional convergence、靜態
Hermitian cross-duality、triple selection、signed reflected convection、static RHS與 fixed-cutoff
separated spacetime identity、limiting finite-Fourier carrier identity、aggregate endpoint cancellation、
compact-time bump、consumer residual span/carriers、ambient-density feasibility gate、全部三槽
cross-window stability、window-free global algebraic tensor、exact image／faithful quotient／residual
factorization、單向 global-image／quotient comparison與 residual naturality，以及
weighted-`lp 1` transverse coefficient到 continuous-field LF test的 bridge；
NS050/NS070 的 global representative與
weak-solution 主線仍未完成，Clay 未解核心的距離仍無法量化。**

## 0.2 持續施工循環：定規則、玩規則、破規則、重建

1. **定規則：**先把 carrier、量詞、invariant、拓撲與驗收 gate 寫成可由 kernel 核對的介面。
2. **玩規則：**在既定介面內盡量推出最強、可重用的結論，保留同一 witness／subsequence，
   不以重選資料掩蓋缺口。
3. **破規則：**用 zero-measure、非零 witness、錯序量詞、norm 偷換、代表元偷渡、ambient-product
   incompatibility 等攻擊，找出「定義可成立但不足以推進 PDE」的邊界。
4. **重建：**把破口變成下一磚的新介面與 honesty gate，再重跑三路審查、全量 build、公理與
   consistency gate。打破的是不足的模型規則，不是 Lean kernel、零 `sorry` 或誠實範圍。

目前一次具體循環是：C202 定出 squared-coordinate norm 規則，C203 在規則內推出 topology
embedding；審查暴露 nonlinear product 尚無 map，C204 以兩層 Hölder 建立 iterated-`L¹`
規則並證九個 ordered products 收斂；再以 nested-window attack 發現 unrestricted product 不足，
C205 補上 restriction laws、product compatibility 與 `L¹_loc` carrier；C206 再用兩層
`L∞×L¹` pairing 證這些 quotient classes 可被固定 bounded-continuous tests 直接消費；C207
用 finite-Fourier derivatives 組出九項 quadratic-gradient functional；C208 把原本過大的
coefficient/field 工作包切開，只先落低風險 cross-Parseval／cross-gradient／Stokes duality。
hostile probe 已證 arbitrary complex data 不能直接混用 Hermitian與 bilinear convention，因此
C209 再只落 triple selection、physical expansion與 reflected coefficient expansion；C210 已做
signed static bridge/RHS，C211 已做 fixed-cutoff weak identity，C212 已做同一 subsequence上的
limiting finite-Fourier identity；C213 再評估 separated-test finite sums；C214 放寬到
aggregate endpoint cancellation；C215 用共用 compact-time bump 給出非平凡可消費族。
C216 定出 ambient residual-jet 規則，unit-initial jet 立即打破「整個 zero-final
kernel 都被殘差消去」；C217 因而重建為僅取 realizable generators 的 algebraic
span，C218 再把 transverse/reality 條件封裝成正確的 complex/real carriers。
C219 將 topology 放到三個 consumer slots 後，又以 continuous residual 打破「projected
realizable span 在 whole ambient consumer 稠密」的 naive 規則。下一輪重建必須把
density 目標縮到 residual kernel，或改用 intrinsic physical test carrier；C219 沒有否定
這兩個正確目標。後續每輪優先打最便宜、最清楚且能被下一層消耗的 abstraction bottleneck。

## 0.3 低成本多人治理：借組織方法，不借武器設計

這套治理只抽取大型科研專案的 coordination pattern，不美化曼哈頓計畫，也不碰武器技術。
[美國國家公園管理局的 Los Alamos 歷史](https://home.nps.gov/articles/000/manhattan-project-science-at-los-alamos.htm)
記錄 Oppenheimer 的跨領域招募，以及 Bethe、Bacher、Kennedy、Parsons 四個 division 的分工；
[DOE 歷史材料](https://ehss.energy.gov/ohre/roadmap/roadmap/part2.html)則記錄 specialized groups、
normal reporting、可直接向 scientific director 升級 blocker，以及任務型 committees。可移植到
本專案的不是軍事目標，而是「一張 mission map、多個可問責小組、內部充分交換、關鍵問題直接
升級」；同一 DOE 史料也記載嚴重的人體實驗倫理失敗，因此本專案另設獨立 honesty/ethics veto：
工程成功不得覆蓋安全、誠實或人的權利。

每輪固定使用下列低成本節奏：

1. root 只定一個可驗收 interface、前置 theorem與明確 NOT-claims；不把 Clay 終局當 sprint。
2. investigator 在 `/tmp` 做最小 compile probe；失敗只回 blocker，不污染正式 module。
3. builder 只升格已綠的窄 theorem package；一磚只跨一個 conceptual boundary。
4. 至少兩個 read-only reviewer加 root lens：一人查型別/API，一人用反例攻 sign、量詞與 vacuity。
5. colloquium checkpoint只交換 convention、counterexample與下一個依賴；正式 repo只接收
   warning-as-error、zero-`sorry`、standard-three-axiom與 full-build皆綠的 artifact。
6. **歷史 C247 GitHub checkpoint（使用者指定的週期保存）：**C236–C247 已完成 targeted build、
   hostile review、root/full build、zero-sorry、standard-three-axiom gate、244/244 consistency、
   registry 與 exact diff；contact code/receipt commits 為 `612e758`／`92e2a97`。161 個 warning
   全是既存 C049–C129 baseline，新十二磚為零。未通過 proof/gate 的中間狀態未送上 GitHub。
7. **歷史 C259 GitHub checkpoint：**C248–C259 已完成 product-gradient／initial／complete consumer
   stability、canonical global-time/spatial bilinear tensor、whole-range realizability、faithful quotient、
   selected residual factorization及單向 global image ≤ all-window image。contact code/receipt commits
   為 `8e89a6c`／`019842c`；256 modules、3424 source declarations、5254 audited declarations、
   256/256 consistency、root/full build、zero-sorry及 standard-three-axiom gate均通過。C220–C259
   沒有新增 warning；161 個 C049–C129 legacy warning仍是同一 baseline。
8. **歷史 C271 GitHub checkpoint：**C260–C262 已完成 one-way exact-image／faithful-quotient
   embedding與 residual naturality；C263–C271 已完成 weighted-`lp 1` transverse coefficient
   carrier、absolute synthesis、normalized multipliers、LF coefficient／continuous-field tests與
   separated pure-tensor pointwise bridge。contact code/receipt commits為
   `d62ff3085b22448116319f458ab3f929d5c91595`／
   `8a7dfd55fcd7c3fdec587d562695f63238a21dd5`；268 modules、3577 source declarations、
   5586 audited declarations與 268/268 consistency均通過。這不補 coefficient reality、LF
   completeness、intrinsic divergence或 density；C271 witness亦未證在 composite range。
9. **目前 C283 GitHub checkpoint：**C272–C275 建 coefficient reality與 real-transverse closed
   carrier；C276–C279 建 reality-preserving continuous symbol synthesis與 transverse diagonal
   coefficient-symbol cancellation；C280–C283 經 native-real target 建 LF transport與一個 explicit
   nonzero in-range witness。contact code/receipt commits為
   `9b08bef28a6849ae53e2381e3ab45001a00f281b`／
   `ff7030b9169114dfa928c8ef5f84d8c14ce9e479`；280 modules、3796 source declarations、
   5943 audited declarations與 280/280 consistency均通過。這不建立 intrinsic derivative、
   divergence、LF completeness、density、weak solution或 Clay result；C283 range theorem也不補
   C271 的不同 tensor-composite range gap。

為了快速喚起分工，採用《咒術迴戰》角色作**工程比喻，不是官方角色設定**（角色名可對照
[動畫官方角色頁](https://jujutsukaisen.jp/character/)）：Megumi＝拆票／備選路線，Gojo＝限時
hard-blocker spike，Nanami＝成本與 scope gate，Nobara＝敵意 honesty review，Shoko＝診斷修復，
Yuji＝整合交付，Sukuna＝只負責找 counterexample、絕不掌握最終決策。角色可以輪換；Lean
kernel、證據與倫理 gate 不可被角色權威取代。

## 1. 已完成的八十個誠實輸出

### 1.1 M61：規格完整性，不是分析進展

`M61_NSIncompressibleSpec` 把下列義務分開放進型別：

1. `IsHarmonic u`：只表示抽象 `hodgeLap u = zero`；
2. `IsDivergenceFree u`：抽象 `div u = 0`；
3. `IsNSSteady ν u`：舊版定常動量式；
4. `IsIncompressibleNSSteady ν u`：2 與 3 的合取。

V2 realization/capstone 會把 div-free 資料一路帶到結論，並保留 V2 → V1 相容橋。
同一模組也證明 `trivialNS` 仍可滿足 V2，防止把 bookkeeping 誤稱為真 NS。

### 1.2 C141：第一個使用真平坦算子的時變 NS 解

對 `ν ≥ 0`，C141 定義

```text
u(t,x,y,z) = exp(-νt) (sin z, cos z, 0),    p(t,x,y,z) = 0
```

並由既有算子逐項證明：

```text
div u = 0
(u · ∇)u = 0
Δu = -u
∂ₜu = -(u · ∇)u - ∇p + νΔu
```

速度 joint `C²`、壓力 joint `C¹`；速度在每個有限時間、每個點皆非零，且
`u(0)=beltramiField`。這是非空洞 PDE anchor，但不是有限能量 `ℝ³` 解，也不是任意初值理論。

### 1.3 C142：真正的 forward 初值介面

`IsFlatNSClassicalSolutionOn I ν u p u₀` 明列：

1. `ν>0`；
2. `0∈I⊆[0,∞)`、`I` order-convex 且含正時間；
3. velocity joint `C²`、pressure joint `C¹`；
4. `div u=0`、以 `HasDerivWithinAt` 表達的動量式、`u(0)=u₀`；
5. time-only pressure gauge invariance。

對抗審查曾構造 singleton-domain 的 within-derivative 空洞路徑；正式修補後，standalone
residual predicate 自帶合法 forward domain 與 `t∈I`，且另證 singleton 不是合法時間域。
常向量場與 C141 衰減場提供非空洞 witnesses。這仍是 supplied-solution interface，不是從任意
`u₀` 建構解。

### 1.4 C143：顯式 mode 的真正有限 `T³` 能量

C143 選定 `T³=(ℝ/2πℤ)³` 的 normalized product Haar probability measure，建立到 mathlib
`UnitAddTorus (Fin 3)` 的 measure-preserving continuous additive equivalence，並將 C141 模式
下降為 `periodicDecay`。對無 `1/2` 的 squared-`L²` 慣例，機器證明：

```text
energy density integrable
E(t) = exp(-2νt)
E'(t) = -2ν E(t)
E(t) > 0
```

這消除了 C141 在 `ℝ³` 上 infinite-energy 的限制，但只對一個 mode；尚未定義 intrinsic torus
NS 微分算子，也不是一般解的 energy identity/inequality。

### 1.5 C144：現有 `T³` carrier 上的 Fourier coefficient 與 Parseval

C144 沿 C143 的保測度等價搬運 mathlib `UnitAddTorus` Fourier theory，得到：

```text
currentT3FourierMonomial n
currentT3FourierMonomial n ∘ projT3 = trigCharE3 (n₀,n₁,n₂)
currentT3FourierCoeff f n = ∫ monomial(-n) • f
∑ ‖currentT3FourierCoeff f n‖² = ∫ ‖f‖²
```

等式對所有 scalar complex `L²` class 成立，且公開 API 使用具名 normalized Haar measure，
不依賴 downstream local instance。這是一般 Fourier 場的第一塊真分析底座；仍未把三個 scalar
components 組成實 velocity、未定義 div-free/multiplier/Leray，也沒有 NS PDE 結論。

### 1.6 C145：三分量 real/complex Parseval 與 zero mode

C145 將 scalar theorem 以有限 `Fin 3` 分量組成 coordinate-product vector `L²`：

```text
CurrentT3ComplexVectorL2 = Fin 3 → Lp ℂ 2 normalizedT3Haar
CurrentT3RealVectorL2    = Fin 3 → Lp ℝ 2 normalizedT3Haar
```

每個平方密度與有限和都先證可積；標準 real-to-complex embedding 只逐 AE 代表元相等，卻精確
保持無 `1/2` 的能量。complex/real 兩版 vector Parseval 均成立，zero coefficient 也精確等於
normalized-Haar componentwise mean。這不是 bundled Bochner vector `Lp`，也尚未施加 mean-zero。

### 1.7 C146：只在 cover 上的 Fourier derivative/Laplacian multiplier

C146 不微分不連續的 `rep/rep3`，而是沿 C144 已證的 pullback equality，在 `E=ℝ³` 上證明：

```text
D_v χ_k = i(k·v)χ_k
D_v²χ_k = -(k·v)²χ_k
Δ_E χ_k = -|k|²χ_k
```

character 的可微性由 C124 真 `HasFDerivAt` discharge，`2π` rescaling 也已在 C144 精確抵消。
這些定理只微分 `currentT3FourierMonomial n ∘ projT3`，不是 intrinsic quotient operator。

### 1.8 C147：有限支撐複向量 Fourier 場的散度符號

C147 以 `FourierFreq3 →₀ (Fin 3 → ℂ)` 表示有限支撐頻譜，並證 lifted coordinate divergence：

```text
div_E (Σ aₙ χₙ) = Σ i(n·aₙ) χₙ.
```

所以每個 supported mode 滿足 `n·aₙ=0` 即推出 cover divergence 為零。零頻率對任意 amplitude
都自動滿足，後續 Leray 必須明定 `P(0)=id`；`n=e₀,a=e₁` 是係數非零、場處處非零的
transverse witness。這仍是複數有限支撐場；單一 mode 不是實速度，欠 `±n` 共軛配對。

### 1.9 C148：有限頻譜的實值共軛對稱

C148 定義正指數慣例下的 `c(-n)=star(c(n))`，明確處理零模態 self-conjugacy，並以 support
取負重索引證有限 lifted synthesis 每分量虛部為零。零族、一般 `±n` constructor、未配對
單模反例與純虛零模外部探針共同驗證定義強度；非零 `±e₀` transverse pair 同時具實值、零
lifted divergence 與 cover 每點非零。這是充分條件，不包含 Fourier 唯一性的 converse。

### 1.10 C149：zero-mode-aware 有限 Leray 投影

C149 對 `n≠0` 使用 `Pₙa=a-((n·a)/|n|²)n`，對 `n=0` 明定 identity。機器證明 range
transverse、fixpoint、idempotence、有限 support inclusion 與 projected lift divergence zero；
非零 longitudinal frequency vector 被送到零，而 transverse unit mode 保持非零，故不是空洞的
zero/identity map。這仍只是 Finsupp coefficient algebra，不是 completed `L²` 上的 bounded
self-adjoint operator。

### 1.11 C150：Stokes dissipation 與 pressure orthogonality

C150 固定 Hermitian pairing，定義無 `1/2` coefficient energy、`|n|²` weighted dissipation、
`-ν|n|²` Stokes symbol 與 `+i n pₙ` pressure-gradient symbol。精確證明 viscous pairing 等於
`-ν` 乘 weighted dissipation，故 `ν≥0` 時實部非正；壓力正交只要求
`u.support ∩ p.support` 上 transverse，且正反 boundary probes 證此交集邊界是 sharp 的。
這是靜態 pairing，尚非沿 ODE 解的 energy derivative。

### 1.12 C151：有限 Fourier 對流能量精確抵消

C151 將 retained convection coefficient 寫成顯式有限 convolution，再把 Hermitian pairing
重排為 `p+q+r=0` 的三重和。對固定 advecting mode，`q↔r` 交換項由 `p·cₚ=0` 精確消去，
所以在只要求 cutoff 取負封閉、係數共軛對稱與逐模態 transverse 時，完整複 pairing 等於零。
不要求 cutoff 對加法封閉；C148 非零 `±e₀` pair 已接入 Finsupp corollary。這仍無時間路徑、
ODE 解、場積分橋或極限程序。

### 1.13 C152：Leray 與 Stokes 保持有限頻譜實值條件

C152 證明 `|−n|²=|n|²`、頻率向量與 wave-dot 的 conjugation/negation 規則，進而得到
`P₋ₙ(star a)=star(Pₙa)`，所以 C149 finite Leray 保持 C148 的係數共軛對稱。它也將 C150
Stokes symbol 包成不增加 support 的 `finiteStokesApply`，證實其對所有實 `ν` 保持同一實值
條件。support 只保證 inclusion：零模與 `ν=0` 可消掉係數。此磚尚未處理 nonlinear convection
或 pressure 的 reality preservation，也沒有 ODE。

### 1.14 C153：保留 cutoff 的有限 Galerkin RHS

C153 先把 C151 raw convection 以顯式 `if k∈s` 截回 Finsupp cutoff；這個 conditional 是必要的，
因為不假設 `s` 對加法封閉。它證 convolution 保持共軛對稱、transverse state 與 Leray-projected
convection 的 Hermitian pairing 不變，再定義
`finiteGalerkinRHS = finiteStokesApply - finiteLerayProject(retainedConvection)`。當
`c.support⊆s`、cutoff 取負封閉、`c` 實值且逐模態 transverse 時，RHS 保持 support、實值與
無散度，且精確滿足 `∑⟨c,RHS(c)⟩=-ν D(c)`。兩個新 map 均有非零 adequacy witness；但這仍是
靜態 map，不是已解出的 ODE，也還沒有時間 energy identity。

### 1.15 C154：固定 cutoff Galerkin ODE 的局部存在

C154 選 `CutoffState s := s → ComplexVelocity3` 作真正有限維 real normed/complete/proper carrier，
以 `cutoffCoeff`／`cutoffRestrict` 的兩向 roundtrip 精確接回 C153 retained Finsupp。它證 C153
coordinate RHS 是 real `C¹`，故 continuous、locally Lipschitz，且在每個 closed ball 上存在一個
Lipschitz 常數；最後直接接 pinned mathlib Picard–Lindelöf，對任意 `ν,s,x₀,t₀` 得到一條在
`t₀` 附近滿足 ODE 的曲線。full `FiniteFourierVelocity` 在目前 instance graph 下不適合作此 ODE
carrier。這只是 ambient complex state 的 local existence；尚未 package uniqueness、實值／無散度
軌道不變、時間能量律或 global continuation。

### 1.16 C155：固定 cutoff Galerkin 解芽的局部唯一性

C155 把 C154 的 locally-Lipschitz vector field 接到 pinned Picard–Lindelöf uniqueness API：兩條
在 `t₀` 經過同一 state 且於 `t₀` 附近滿足同一 ODE 的曲線 eventually 相等，並另給出縮小到
非空 `Ioo` 後的 reader-facing 版本。與 C154 合併後可得到「存在一條 solution germ，且所有
同初值 solution germs 在更小鄰域相同」。這不是原始任意 interval 上的唯一性、maximal solution
或 global uniqueness。

### 1.17 C156：無散度條件的 whole-interval 軌道不變

C156 不只重用 C153 的 static tangency，而是逐 mode 推出 exact defect ODE
`(k·cₖ)' = -ν|k|²(k·cₖ)`，再證複純量線性 ODE 的零初值解在共同 open interval 上恆零。
因此 initially transverse 的 Galerkin trajectory 在其整個給定 `Ioo` 上保持 transverse，並可把
C154 的局部解強化成 transverse local solution。這仍未處理 coefficient reality 或 global
continuation。

### 1.18 C157：actual solution 上的 pointwise energy derivative

C157 定義無 `1/2` 的 cutoff coordinate energy，給出能量等於 `1` 的非零 transverse singleton
witness，並精確橋接 C150 的 Finsupp energy。對每個當下同時滿足 ODE、共軛對稱與 transverse
條件的時間點，機器證明 `E'=-2νD`；係數 `2` 正是因 energy 未除以二。此處尚未積分時間、
推出 monotonicity/a priori bound，或建立 global continuation。

### 1.19 C158：實值條件的 solution-germ 不變性

C158 在取負封閉 cutoff 上定義 conjugate-reflection，證 retained convection 與完整 Galerkin RHS
對它 equivariant，且其 fixed points 精確等價於 C148 conjugate symmetry。把一條 solution 做
reflection 後仍是同 ODE solution，故可用 C155 解芽唯一性證 initially real 的曲線在 `t₀` 附近
eventually real。結論刻意只到 germ；尚未聲稱整個原 interval 或全域 reality invariance。

### 1.20 C159：同一局部 admissible 解與 energy law

C159 將 C154–C158 組裝成單一 theorem：對取負封閉 cutoff、initially real 且 transverse 的 state，
存在同一條曲線與同一個非空 open interval，其上同時滿足 exact Galerkin ODE、coefficient reality、
modewise transversality 與 pointwise `E'=-2νD`。support 由 cutoff coordinate carrier 自動保證。
這仍是固定 cutoff 的局部有限維結果；沒有 integrated energy estimate、global finite-cutoff
solution、cutoff-uniform bound、PDE limit 或 Clay regularity 結論。

### 1.21 C160：非負黏度下的 local energy monotonicity

C160 將 C159 的 actual pointwise derivative、C150 的 weighted dissipation 非負性與 real
mean-value theorem 接起來。當 `ν≥0`，同一 local admissible Galerkin curve 的 cutoff energy
在同一正半徑 `Ioo` 上 `AntitoneOn`；對 interval 內的 forward times `t₀≤t`，得到明確上界
`E(t)≤E(t₀)=E(x₀)`。headline 保留 ODE、reality、transversality 與 energy derivative，避免
用無關常數曲線製造空洞能量敘述。這仍非 integrated identity，不含 endpoints、strict decay、
state-norm bound、global continuation、cutoff-uniform estimate 或 PDE limit。

### 1.22 C161：compact subinterval 上的 exact integrated energy balance

C161 先將 `finiteFourierWeightedDissipation (cutoffCoeff s x)` 改寫為固定 subtype `s`
上的有限和，再由 solution curve 的 `HasDerivAt` 證該耗散量在每個閉子區間
continuous 與 interval-integrable。因此 FTC-2 可把 pointwise `E'=-2nuD` 精確積分為
`E(b)+2nu∫ₐᵇD(t)dt=E(a)`；等式對任意 `nu` 成立，端點必須嚴格位於 local
open interval 內。headline 在 `nu≥0` 時保留 C160 同一條曲線的 ODE、reality、
transversality、pointwise law、antitonicity 與 forward bound。這仍是 local fixed-cutoff
coefficient identity；尚無 carrier-norm bound、global continuation、cutoff-uniform estimate 或 PDE limit。

### 1.23 C162：coefficient energy 到 actual cutoff-state norm

C162 針對 C154 真正作為 ODE carrier 的 `CutoffState s = s → Fin 3 → ℂ`。這個
nested finite Pi 型別使用 supremum norm；由每個座標平方都不超過全部座標平方和，
得到 `||x||^2≤E(x)` 與 `||x||≤sqrt(E(x))`。在 C161 同一條 `nu≥0` local
admissible curve 上，forward energy bound 因而轉成
`||alpha(t)||≤sqrt(E(x₀))`。headline 原樣保留 pointwise/integrated laws 與所有
constraints。這是 continuation 所需的 norm-boundedness 輸入，但尚未建立 enlarged
closed-ball extension、maximal interval 或 global fixed-cutoff solution；右邊初始能量也可隨
cutoff 改變，故不是 cutoff-uniform PDE estimate。

### 1.24 C163：bounded state ball 上的 uniform local restart

C163 在 inner `closedBall 0 R` 外取 radius `R+1`，由 closed-ball Lipschitz estimate 與
`RHS(0)` 得共同的 `K,L`，再令 `delta=1/(L+1)>0`。同一個 `delta` 對 ball 內每個 state
與每個 center time 都可套 Picard–Lindelöf；結論同時保存 closed `Icc` 上的
`HasDerivWithinAt` 與 interior 的 `HasDerivAt`。把 `R` 取成 `sqrt(E(x₀))` 即直接接上 C162。
它仍只是 local solution family，不含 flow law、舊解相容性、piecewise gluing 或 global existence。

### 1.25 C164：common compact interval uniqueness 與 whole-Icc reality

C164 將兩條 `ContinuousOn (Icc a b)` solution curves 的 compact images 包入同一個 state ball，
再以 C154 ball-Lipschitz constant 與 `ODE_solution_unique_of_mem_Icc` 證：只要它們在一個
interior time 相等，就在完整 `Icc`（含 endpoints）相等。另一版本直接接受 C163 回傳的
within-derivatives。把 competitor 取為 conjugate-reflection 後，C158 的 reality germ 因而升成
whole-`Icc` reality。這是 gluing 所需 uniqueness，不是 gluing 或 extension 本身。

### 1.26 C165：compact-support global ODE engine

C165 證明 complete real normed space 上每個 `C¹` compactly-supported autonomous vector field
都有全時間 integral curve。Compact support 給 global Lipschitz constant 與 RHS norm bound，
統一 Picard time window 再交給 mathlib manifold `UniformTime` glue；最後轉回 repository 使用的
`∀t, HasDerivAt` 介面。只 package existence，不冒稱 flow law 或 Galerkin field 本身 compact。

### 1.27 C166：energy-bump global modified Galerkin solution

C166 證 `cutoffEnergy` 為 `C¹`，並由 C162 coercivity 把 `x↦b(E(x))` 的 support 包進
finite-dimensional compact ball。C165 因而給 `x'=b(E(x))•RHS(x)` 的 all-time solution；另證
energy 在 conjugate-reflection 下不變。這一層明確仍是 modified ODE。

### 1.28 C167：modified dynamics 的 global admissibility 與 scaled energy

C167 用 modified field global uniqueness 證 reality，並對每個 longitudinal defect 建立
time-dependent scalar complex ODE，以 `0≤b≤1` 對 zero solution 套 global uniqueness，得到
transversality。Quadratic chain rule與 exact Galerkin pairing再給
`E'=b(E)(-2nuD)`；所有性質 package 在同一條 global modified curve。

### 1.29 C168：original fixed-cutoff forward-global existence

C168 選 inner/outer radii `E(x₀)+1`、`E(x₀)+2` 的 genuine smooth bump。`nu≥0` 時 scaled
energy derivative nonpositive，所以 `t≥0` 有 `E(t)≤E(x₀)`，bump 在整條 forward trajectory
精確為 1；同一 curve 遂在每個 `t≥0` 解原始 Galerkin RHS。Headline 保留 all-time auxiliary
modified equation、global reality/transversality、forward exact pointwise energy law、energy bound
與 `||alpha(t)||≤sqrt(E(x₀))`。負時間沒有冒充 original dynamics。

### 1.30 C169：由初始端點起算的 forward-global integrated energy

C169 不再要求 endpoints 嚴格位於 local open interval；它直接在任意 `0≤a≤b` 上由 finite sum
證 dissipation continuous/integrable，故包括 `a=0`，再以 FTC 得
`E(b)+2nu∫ₐᵇD(t)dt=E(a)`。Headline 把所有 compact forward interval balances 接在 C168
同一條 forward-global admissible curve 上。仍只是 fixed-cutoff coefficient identity。

### 1.31 C170：任意 left endpoint 的 whole-forward-ray uniqueness

C170 對每個 `t≥t₀` 把兩條 forward solutions 在 `Icc t₀ t` 的 compact images 放入同一 state
ball，由 C154 的 ball-Lipschitz constant 與 mathlib one-sided ODE uniqueness 得
`EqOn alpha beta (Ici t₀)`。這不需 `nu≥0`、reality、transversality 或 energy hypothesis；但兩條
curves 必須已解同一 fixed-cutoff ODE，故不是 PDE uniqueness 或 cutoff-uniform stability。

### 1.32 C171：任意初始時間的 unique forward-global 完整能量包

C171 將 C169 curve 平移為 `alpha(t)=gamma(t-t₀)`，在任意 prescribed time 通過同一 initial
state。原 Galerkin ODE、pointwise energy derivative、energy/carrier-norm bounds 與所有
`t₀≤a≤b` integrated balances 都只在 forward region 宣告；all-time 部分仍明列為 auxiliary
modified ODE。C170 再把此 curve 證成所有同初值 forward competitors 中唯一。

### 1.33 C172：nested cutoffs 與第一條共同 L² bound

C172 建立 canonical cubes `[-N,N]³∩ℤ³` 的 exact membership、negation closure 與 nesting，
並重用 `Finset.restrict₂` 證 cutoff state zero-extension/restriction compatibility。同一
`CurrentT3RealVectorL2` field 的 finite Fourier projections restriction-compatible，且 C145
Parseval 給

```text
E_s(initial) ≤ E_t(initial) ≤ E_L²(full field),    s ⊆ t.
```

對每個 separately admissible cutoff，C171 因而提供 unique forward-global solution，滿足
`E_s(alpha(t))≤E_L²` 及 `||alpha(t)||≤sqrt(E_L²)` 的共同數值界。這沒有建構 jointly chosen／
coherent trajectory family；也尚未由 arbitrary real `L²` 自動導出 coefficient reality 或
divergence-free，因此仍不能做 compactness 或 PDE limit。

### 1.34 C173：real L² Fourier coefficient 的 conjugate symmetry

C173 直接對 C144 的 normalized-Haar integral 取共軶，並用 canonical
real-to-complex `Lp` map 的 almost-everywhere representative identity，證明

```text
currentT3RealVectorFourierCoeff u (-n)
  = star (currentT3RealVectorFourierCoeff u n).
```

這消去 C172 對任意 real `L²` datum 的額外 coefficient-reality 假設。它不會將
real-valuedness 誤當成 incompressibility；wave-vector transversality 必須另由 Leray 投影得到。

### 1.35 C174：finite Leray 的精確 Pythagoras 與 energy contraction

C174 令 `p=Pₙa`、`r=a-p`。C149 給 `n·p=0`，C153 的 Hermitian bridge 給
`⟨p,p⟩=⟨p,a⟩`，因此 `⟨p,r⟩=0`。由 C150 的 self-pairing/energy 關係得

```text
E(Pₙa) + E(a - Pₙa) = E(a).
```

結果不只 modewise energy 不增，`finiteFourierEnergy` 與
`finiteFourierWeightedDissipation` 也都不增。這是 finite coefficient 定理，不是已建立
completed `L²` 上的 bounded/self-adjoint Leray operator。

### 1.36 C175：arbitrary real L² datum 自動產生 admissible cube initial states

C175 定義一個全域 coefficient family

```text
cᴾ_u(n) = Pₙ (û(n)),
```

然後才將它 restriction 到每個 cube。所以 nested initial states 的 `Finset.restrict₂`
compatibility 是定義等式，同時 C173/C152 提供 reality，C149 提供 transversality，
C174/C172 提供

```text
E_N(Pû) ≤ E_M(Pû) ≤ E_L²(u),    N ≤ M.
```

因此對每個 `N`，C171 不再需要 caller 另給 `hreal/hdiv`，就能啟動 unique
forward-global Galerkin solution。這裡的 coherence **只是 initial restriction coherence**；大 cube 的
nonlinear convolution 可回灌低頻，所以 trajectories 一般不會在 restriction 後相等。

### 1.37 C176：第一條 cube-independent time-integrated dissipation bound

C176 從 C175/C171 的 exact balance

```text
E_N(b) + 2ν ∫ₐᵇ D_N(t) dt = E_N(a)
```

與 `E_N(b)≥0`、`E_N(a)≤E_L²(u)` 導出

```text
2ν ∫ₐᵇ D_N(t) dt ≤ E_L²(u),
∫ₐᵇ D_N(t) dt ≤ E_L²(u)/(2ν)    if ν>0.
```

RHS 不含 `N`，這是進入 compactness 路線的第一個真正 common-in-cutoff 時間積分界。
然而 `D_N` 仍是 finite coefficient sum；尚未在同一 field space 辨識為 `H¹` seminorm，
也沒有 time derivative 界或 compactness theorem。

### 1.38 C177：exhaustive cubes 與 initial coefficient-energy tails

C177 以三個 integer coordinates 的 `natAbs` 構造明確半徑，證明 canonical cubes 覆蓋
全部 `ℤ³` frequencies，並對 finite frequency sets cofinal。因為一般 index type 的 `HasSum`
本來就是 Finset `atTop` 上的極限，C145 Parseval 可直接沿此 cofinal map 得到

```text
E_N(raw û) → E_L²(u),
E_L²(u) - E_N(raw û) → 0.
```

對 `Pû`，C174 的 modewise contraction 先給 summability，再定義

```text
E_coeff(Pu) = Σ_n E(P_n û(n)) ≤ E_L²(u).
```

Projected cube energies 趨向 `E_coeff(Pu)`；此外 cube partial energy 加上 cube 外 subtype
`tsum` tail 精確等於 total，而 actual tail 趨零。若 raw coefficients 已逐 mode transverse，
則 `P_n û(n)=û(n)`，此時才有 `E_coeff(Pu)=E_L²(u)`。這結束 initial coefficient limit，
但仍未建 completed field-level Leray operator、trajectory convergence 或任何 PDE compactness。

### 1.39 C178：共同 quotient-torus `L²` finite-field reconstruction

C178 將任意 finite Fourier coefficient family 合成為 genuine continuous `T³` complex vector
field，並送入共同的 coordinate-product `L²` carrier。沿 `projT3` 拉回後，它精確等於 C147
的 cover synthesis；conjugate-symmetric coefficients 給 quotient-torus pointwise reality。
Orthonormal Fourier modes 再給 exact Parseval identity

```text
E_L²(U_c) = E_coeff(c).
```

Cutoff-state wrapper 將每個 Galerkin state 放入同一 carrier。這仍是 finite Fourier synthesis，
不是 tangent-bundle section、completed-space Leray operator、跨 cutoff convergence 或 PDE 解。

### 1.40 C179：finite-field homogeneous gradient energy

C179 對每個方向定義 multiplier field `∂_j U_c`，其 coefficient symbol 是 `i n_j`。它不只
替新物件命名：沿 Euclidean cover 的 pullback 被證明等於 C178 finite synthesis 的實際
coordinate derivative。Fourier orthonormality給出

```text
Σ_j E_L²(∂_j U_c) = D(c),
```

並對 cutoff states 包成 `cutoffStateGradientEnergyT3L2`。左側是 finite-field homogeneous
gradient seminorm squared；未構造一般 intrinsic derivative、完整 `H¹` norm 或 Sobolev completion。

### 1.41 C180：field-level spacetime gradient bound

C180 將 C176 的每條 cube Galerkin coefficient trajectory timewise 重建到 C178 的共同
`T³` complex `L²` carrier。利用 C178/C179 的 exact identities，C176 的 balance 成為

```text
E_L²(U_N(b)) + 2ν ∫ₐᵇ E_L²(∇U_N(t)) dt = E_L²(U_N(a)).
```

因此 `ν≥0` 有 viscosity-weighted bound；`ν>0` 才有
`∫ₐᵇE_L²(∇U_N)≤E_L²(u)/(2ν)`。Headline 保留 Leray/cube projected initial state、原始
finite Galerkin ODE 與 forward uniqueness。各 `N` 的 trajectory 仍分別存在；尚無
cutoff-indexed selection、field-time regularity、compactness、nonlinear limit 或弱 PDE 解。

### 1.42 C181：cutoff-indexed common-field trajectory family

C181 將 C180 的量詞由「對每個 `N` 分別存在」包成一個 dependent family

```text
alpha : (N : ℕ) → ℝ → CutoffState (fourierCubeCutoff N),
U     : ℕ → ℝ → CurrentT3ComplexVectorL2.
```

一次 `Classical.choice` 對每個 `N` 選取同一條同時滿足 projected initial condition、forward
Galerkin ODE、field energy bound、weighted spacetime-gradient bound、exact balance 與 forward
uniqueness 的 curve；`ν>0` 的 unweighted bound 從同一 family 推出，不另選第二族。這是後續
compactness statements 所需的量詞介面，但只是 noncomputable selection：沒有 cross-cutoff
coherence、common-carrier time regularity、Cauchy/convergence/subsequence 或 PDE limit；這些
後續介面中，per-cutoff continuity 與 negative-space time control 分別由 C182、C188–C192 補上。
fixed-low-mode field equicontinuity、integrated high tail 與 static compact closure 則由
C193–C195 補上；在 `ν>0` 時，C196–C198 隨後完成每個 fixed interval 的 full-family relative
compactness 與 strong subsequence，C199–C211 再完成共同 exhaustion subsequence、local limit
compatibility、projective carriers、coordinate norm bridge、scalar-coordinate embedding、
coordinate-product convergence、outer-time cross-window compatibility、fixed-test pairings、
finite-Fourier quadratic-gradient functionals、Hermitian cross-duality、signed static RHS與
fixed-cutoff separated spacetime identity；
global representative 與 PDE identification 仍未完成。

### 1.43 C182：common-carrier time continuity

C182 將 C178 finite synthesis 寫成 `Finsupp.lsum` complex linear map，將 fixed-cutoff zero
extension 也綁成 complex linear map，再利用 finite-dimensional source 證其 composition

```text
cutoffStateT3L2CLM : CutoffState s →L[ℂ] CurrentT3ComplexVectorL2
```

continuous。任意 continuous coefficient curve 因而能 transport 成 common-carrier continuous
field curve；C181 每個 selected trajectory 的 forward `HasDerivAt` certificate 遂給
`ContinuousOn U_N (Ici t₀)`。這是逐 `N` 的 continuity，沒有 cutoff-uniform modulus、
equicontinuity、field-valued time derivative、negative-Sobolev bound 或 compactness。C188–C192
後來在另一個 common negative coefficient carrier 中補上 uniform squared increment estimate
及 equicontinuity；C194 再把每個 fixed low-mode projection 搬回 field `L²` equicontinuity，
C195 給 static spatial compact closure；在 `ν>0` 時，C196–C198 再完成 fixed-window full-family
compact closure/subsequence，C199–C211 再完成 exhaustion diagonalization、local
compatibility/carriers、coordinate norm bridge、scalar-coordinate embedding、coordinate-product
convergence、outer-time cross-window compatibility、fixed-test pairings、finite-Fourier
quadratic-gradient functionals、Hermitian cross-duality、signed static RHS與 fixed-cutoff
separated spacetime identity。這些仍不是具 global
representative 的 trajectory 或 PDE limit。

### 1.44 C183：各向同性 `H⁻³` lattice weight

C183 定義真正的 isotropic coefficient weight

```text
w₋₃(n) = (1 + |n|²)⁻³
```

並以一維 inverse-square summability、三重 product majorant 與
`(1+a)(1+b)(1+c) ≤ (1+a+b+c)³` 證明它在 `ℤ³` 可加。有限係數 energy
`∑ₙw₋₃(n)E(cₙ)` 非負且不超過普通 coefficient energy，並有 actual cutoff-state sum
公式。這一磚尚只是 weight 與 finite quadratic functional，不把它誤稱 completed Sobolev
space。

### 1.45 C184：complete common Fourier `H⁻³` coefficient carrier

C184 把 physical coefficient 乘以 `sqrt w₋₃(n)` 後送入

```text
CurrentT3FourierHminusThree = Fin 3 → ℓ²(ℤ³; ℂ).
```

這是 pin 上有 genuine `CompleteSpace` instance、且與 cutoff 無關的 common carrier。逐 mode
除回 strictly positive multiplier 可精確 recovery，所以 finite embedding injective；carrier
quadratic energy 精確等於 C183 weighted energy。尚未證與 intrinsic distributional torus
Sobolev 定義等價，也沒有一般 Fourier transform／inverse synthesis。

### 1.46 C185：cutoff-independent per-mode convection bound

C185 對固定 output frequency 證明

```text
E(Bₛ(c,c)(k)) ≤ E(c) D(c).
```

fixed-sum pair set `{(p,q)∈s² | p+q=k}` 的 `fst` 與 `snd` 都是 injective；配合
Cauchy--Schwarz，兩個 factors 分別嵌入 full energy 與 weighted dissipation，因此常數為 `1`
且不帶 `#s`。同一界在 modewise Leray projection 後仍成立。這只是逐 mode，不可直接冒充
完整 `ℓ²` 或 time-derivative bound。

### 1.47 C186：summed `H⁻³` projected-convection bound

C186 定義並核證 finite positive lattice constant

```text
C₋₃ = ∑' n : ℤ³, w₋₃(n)
```

先證 finite Leray projection contract C183 weighted energy，再於 genuine retained output support
逐 mode 套 C185，最後以 `Summable.sum_le_tsum` 得

```text
E_H⁻³(P Bₛ(c,c)) ≤ C₋₃ E(c) D(c).
```

右端完全不含 cutoff radius/cardinality，並有 C184 common-carrier 版本。這關掉 nonlinear
negative-space estimate 的核心 algebraic 缺口；viscous/full RHS 隨後由 C187 關掉，trajectory
transport、time integral、FTC、squared increment 與 equicontinuity 再由 C188–C192 補上；
high-tail／static spatial inputs由 C193–C195 補上。在 `ν>0` 時，full trajectory compactness、
subsequence 的 fixed-window 版本由 C196–C198 補上；C199–C211 再補共同 exhaustion subsequence、
local compatibility/projective carriers、coordinate norm bridge、scalar-coordinate embedding、
coordinate-product convergence、outer-time cross-window compatibility、fixed-test pairings、
finite-Fourier quadratic-gradient functionals、Hermitian cross-duality、signed static RHS與
fixed-cutoff separated spacetime identity。
global representative 與 weak PDE limit 仍缺。

### 1.48 C187：full static Galerkin RHS `H⁻³` bound

C187 先證一般 coordinate energy difference 的 factor-two estimate，再核對 Stokes mode 的
exact energy 為 `ν²|n|⁴E(cₙ)`，並以

```text
(1 + |n|²)⁻³ |n|⁴ ≤ 1
```

得到 `E_H⁻³(Stokes_ν c)≤ν²E(c)`。與 C186 projected-convection bound 合併後，對任意 finite
coefficient family（不需 `support c ⊆ s`）有

```text
E_H⁻³(RHSₛ(c)) ≤ 2ν²E(c) + 2C₋₃E(c)D(c).
```

common-carrier 版本沒有額外 norm conversion。這完成 static negative-space RHS package；
C188–C192 已在後續完成 trajectory transport、積分、FTC、squared increment 與 equicontinuity。

### 1.49 C188：actual trajectory derivative 的 `H⁻³` transport

C188 把 finite weighted embedding 綁成 complex linear map，並利用 fixed-cutoff source 的
finite-dimensionality，得到送入共同 complete carrier 的 continuous linear map。對 actual
cutoff Galerkin RHS 證明 zero-extension 與 C153 full finite RHS 的精確相等，因此 C181 每條
selected trajectory 的 ODE certificate 可直接 transport 成

```text
HasDerivAt U_N(t) (RHS_N(t)).
```

結合 C187、C181 的 uniform energy bound，得到每個 forward time 的 pointwise estimate

```text
E_H⁻³(RHS_N(t)) ≤ 2ν²E₀ + 2C₋₃E₀D_N(t).
```

這是 actual selected nonlinear finite system 的 derivative，不是 proxy curve；但單點估計本身
仍不是 time integral、compactness 或 PDE limit。

### 1.50 C189：cutoff-independent integrated squared RHS-energy

C189 先由 trajectory/RHS continuity 證明 scalar RHS-energy 與 dissipation 在每個 fixed forward
compact interval 上真正 `IntervalIntegrable`；沒有依賴「不可積時 interval integral 定義成零」的
空洞捷徑。對 `ν>0`、`t₀≤a≤b`，將 C188 pointwise estimate 與 C181 integrated dissipation 合成

```text
∫ₐᵇ E_H⁻³(RHS_N(t)) dt
  ≤ 2ν²E₀(b-a) + (C₋₃/ν)E₀².
```

右端不含 `N`。這是一條 squared coefficient-energy integral，不等同於已建 intrinsic
`L²_tH⁻³_x` Sobolev object，也不單獨給 compactness。

### 1.51 C190：common carrier 中的 Bochner integrability 與 exact FTC

C190 證明沿每條 selected family member 的 embedded Galerkin RHS 在 forward compact intervals
上 continuous，故真正 Bochner interval-integrable。利用 C188 的 transported derivative 與
complete carrier 的 Banach FTC，對任意 real viscosity 證

```text
∫ₐᵇ RHS_N(t) dt = U_N(b) - U_N(a).
```

這是 exact endpoint identity；它本身沒有 cutoff-independent norm bound，也沒有抽取 subsequence。

### 1.52 C191：cutoff-independent squared time-increment estimate

C191 先證 common carrier 的 inherited finite-product norm 滿足
`‖v‖²≤E_H⁻³(v)`，再於 restricted time interval 用真正 Bochner integrability 與 Hölder/Cauchy--
Schwarz 證

```text
‖∫ₐᵇ f(t) dt‖² ≤ (b-a) ∫ₐᵇ E_H⁻³(f(t)) dt.
```

代入 C189 與 C190 後，對 `ν>0`、`t₀≤a≤b` 得

```text
‖U_N(b)-U_N(a)‖²
  ≤ (b-a) (2ν²E₀(b-a) + (C₋₃/ν)E₀²).
```

右端不含 `N` 且隨 `b-a→0⁺` 趨零。C191 本身是平方範數版本；C192 已另 package square-root
corollary 與 standard equicontinuity predicates，但仍未證 `HolderOnWith`。更重要的是，
infinite-dimensional negative carrier 中的 uniform time control 不等於 spatial compactness，也
不是 weak solution 或三維 smoothness。

### 1.53 C192：whole-forward-ray cutoff-uniform `H⁻³` equicontinuity

C192 定義初始能量 `E₀` 對應的顯式 modulus

```text
ω(h) = sqrt (h (2ν²E₀h + (C₋₃/ν)E₀²))
```

並證 `ω(h)→0` as `h→0`。先由 `Real.le_sqrt_of_sq_le` 取 C191 的平方根，再以
`le_total a b` 交換 reversed endpoints，對任意 `a,b≥t₀` 得

```text
dist (U_N(a)) (U_N(b)) ≤ ω(dist a b).
```

同一 `ω` 不含 `N` 或絕對時間。把 domain 限制為 `Ici t₀` subtype 後套 mathlib 的
continuity-modulus theorem，再由 `uniformEquicontinuous_restrict_iff` 返回原時間軸，正式得到

```text
UniformEquicontinuousOn (fun N ↦ U_N) (Ici t₀)
```

與 `EquicontinuousOn` corollary；另有 concrete selected family wrapper。這個結論比 fixed compact
window 稍強，但 codomain 仍是 coefficient `H⁻³` carrier，而非 field `L²`。因此它不是 pointwise
relative compactness、Arzelà--Ascoli、subsequence extraction、weak PDE limit 或 smoothness。

### 1.54 C193：common-field Fourier high tail 與 outer-cutoff-uniform spacetime tail

C193 以 actual Finsupp filter 定義 `low_M c` 與 `high_M c`。若頻率不在 radius-`M` cube，
至少有一個整數座標滿足 `M+1≤|n_i|`，所以

```text
(M+1)² ≤ |n|²,
(M+1)² E(high_M c) ≤ D(c).
```

low/high 精確分割、C182 linear synthesis 與 C178 Parseval 進一步給

```text
(M+1)² ‖S(c)-S(low_M c)‖² ≤ D(c).
```

這裡 common carrier 的 norm 是三座標 Pi-sup norm；proof 只用已證的
`‖v‖²≤currentT3VectorL2Energy(v)`，沒有把它冒充能量 sum。沿 C181 actual family，tail 與
dissipation integrands 均由 trajectory continuity 真正證為 `IntervalIntegrable`，再套 field
gradient bound 得

```text
∫ₐᵇ ‖U_N(t)-P_MU_N(t)‖² dt ≤ E₀ / (2ν(M+1)²).
```

右端不依賴 outer cutoff `N`。它是 integrated tail，不是 pointwise 或 `sup_t` tail，也尚未是
bundled spacetime `Lp` compactness。

### 1.55 C194：fixed-low-mode recovery 與 common-field `L²` equicontinuity

C194 對每個有限頻率集合 `s`，以 `lp.evalCLM` 取 C184 weighted carrier 座標，再除以嚴格
正的 multiplier，與 C182 synthesis 組成 continuous linear map

```text
T_s : CurrentT3FourierHminusThree →L[ℂ] CurrentT3ComplexVectorL2.
```

逐 mode inverse cancellation 證 `T_s` 精確恢復 physical coefficients；當
`s=fourierCubeCutoff M` 時，它作用在第 `N` 條 embedded trajectory 上恰等於 C193 的 `P_MU_N`。
將 C192 modulus 經 `T_M.le_opNorm` 搬運後，對每個固定 `M` 得

```text
UniformEquicontinuousOn (fun N ↦ P_M U_N) (Ici t₀)
```

於 common field `L²` carrier。`‖T_M‖` 依賴 `M`，所以這不是 M-uniform 或 full-field
equicontinuity；高模態仍需 C193 的 integrated tail 處理。

### 1.56 C195：static finite-Fourier Rellich input

C195 定義 common-field sublevel：存在 finite coefficients `c`，且同時
`E(c)≤E₀`、`D(c)≤D₀`。對任意 `ε>0`，先選 `M` 使 C193 high tail `<ε/2`；fixed-low-mode
coefficients 位於 finite-dimensional `CutoffState (fourierCubeCutoff M)` 的 energy-controlled
closed ball，其 continuous synthesis image compact，因此有 finite `ε/2` cover。triangle inequality
給原 sublevel finite `ε` cover，正式得到

```text
TotallyBounded (finiteFourierEnergyDissipationSublevel E₀ D₀)
IsCompact (closure (finiteFourierEnergyDissipationSublevel E₀ D₀))
```

原 sublevel 未證 closed，因此只宣稱 closure compact。更重要的是，C181 對 `D_N` 只有時間積分
界，沒有共同 pointwise `D_N(t)≤D₀`；所以 C195 是 genuine static spatial compactness input，
不能直接逐時套到 actual trajectory family。C196–C198 已改走 fixed-low-mode compact-time
Ascoli 加 C193 integrated tail 的路線，得到下述 fixed-window compactness theorem。

### 1.57 C196：fixed-low-mode compact-time Arzelà--Ascoli

C196 對每個固定 `M`，把 `P_MU_N` 限制到 compact time subtype `Icc a b`，包成 bounded
continuous paths。共同 energy bound 把所有 path values 放進 finite-dimensional cutoff-state
closed ball 的 continuous synthesis image；該 image compact，而 C194 給整族 equicontinuity。
因此 mathlib 的 Arzelà--Ascoli theorem 給

```text
IsCompact (closure {low-mode bounded path at outer cutoff N | N : ℕ}).
```

結論使用 uniform path metric，對 `a>b` 的空 subtype 也合法。它只固定 `M`；C193 的 high tail
僅在時間積分後變小，所以不能由此聲稱 full fields 在 uniform topology 中 compact。

### 1.58 C197：fixed-low-mode iterated spacetime carrier compactness

C197 定義 closed-interval subtype 上未正規化的 Lebesgue pullback measure

```text
compactIntervalVolume a b = Measure.comap Subtype.val volume
CurrentT3CompactIntervalL2 a b =
  Lp CurrentT3ComplexVectorL2 2 (compactIntervalVolume a b).
```

`BoundedContinuousFunction.toLp` 是 continuous complex-linear map，故 C196 的 compact path
closure 經其 image 仍 compact，並包含全部 fixed-`M` low-mode `Lp` family 的 closure。內層
`CurrentT3ComplexVectorL2 = Fin 3 → Lp ℂ 2` 使用 Pi/sup norm；尚未證這個 iterated norm 等價於
standard joint product-measure Euclidean-vector `L²([a,b]×T³;ℂ³)`。C197 也尚未自行吸收 high tail。

### 1.59 C198：full-family fixed-window compactness 與 cutoff subsequence

C198 先證 C197 path-to-`Lp` map 的 exact norm identity，再把 subtype integral 轉成 oriented
interval integral：

```text
‖U_N - P_MU_N‖²_CurrentT3CompactIntervalL2
  = ∫ₐᵇ ‖U_N(t)-P_MU_N(t)‖² dt.
```

因此 C193 給右側一致 high-tail bound。對任意 `ε>0` 選一個 `M` 令此 tail `<ε/2`，再以
C197 的 fixed-low-mode compact family 取得 finite `ε/2` cover，triangle inequality 證 full
Galerkin family `TotallyBounded`。carrier 完備，故其 closure compact；compact sequential
extraction 進一步給

```text
∃ U, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (U_(φ k)) atTop (𝓝 U).
```

這是每個固定 `t₀≤a≤b` 上，在 C197 iterated carrier 中的強收斂子序列。`U` 是抽象 quotient
`Lp` element，`φ` 與 `U` 可依賴區間；尚無 whole-forward-ray diagonalization、cross-interval
compatibility、代表元、initial trace、real/div-free preservation、linear/quadratic term passage、
energy inequality、weak Navier--Stokes equation 或 Leray--Hopf package。

### 1.60 C199：integer exhaustion 上的一條共同 diagonal subsequence

C199 定義 dependent product

```text
CurrentT3ForwardExhaustionL2 t₀ =
  (m : ℕ) → CurrentT3CompactIntervalL2 t₀ (t₀+m).
```

每個 coordinate 使用 C198 的 compact closure；`isCompact_pi_infinite` 將它們組成 compact
product。actual sequence `N ↦ (m ↦ U_N|[t₀,t₀+m])` 落在該 product，且 actual product range 的
closure 是其 compact closed subset。countable Pi 自動 first-countable，因此一次
`IsCompact.tendsto_subseq` 得

```text
∃ U, ∃ φ, StrictMono φ ∧
  U ∈ closure(actual product family) ∧
  ∀ m, U_(φ k)|[t₀,t₀+m] → U m.
```

同一 `φ` 在 `∀m` 外，正式關掉「每個 interval 各抽不同 subsequence」的量詞缺口。C199
本身尚未定義不同 coordinate carriers 間的 restriction；`m=0` 是 zero-measure coordinate，
也沒有宣稱 product point 是 single global forward-ray `L²` element。

### 1.61 C200：nested-window restriction 與 compatible local limits

C200 對同一左端點且 `b≤c` 定義 inclusion `Icc a b → Icc a c`。short interval measure 等於
long interval measure 沿 inclusion 的 comap；inclusion 對 long measure restricted to its
measurable range measure-preserving。由 `LpToLpRestrictCLM` 與
`Lp.compMeasurePreservingₗᵢ` 合成

```text
R_b^c : CurrentT3CompactIntervalL2 a c →L[ℂ]
          CurrentT3CompactIntervalL2 a b,
‖R_b^c f‖ ≤ ‖f‖.
```

C200 證 `R_b^c` a.e. 就是 composition with inclusion，與 bounded continuous path 的 `toLp`
及 actual Galerkin `fullCompactIntervalL2` 精確 commute。若同一 cutoff subsequence 在大小窗
分別趨向 `U_c,U_b`，continuity 與 limit uniqueness 給 `R_b^c U_c=U_b`。套 C199 得一族
compatible local quotient classes：所有 `m≤n` 均有 `R_m^n(U n)=U m`。

這仍不是已 glue 的 global measurable velocity representative，也不自動保留 initial trace、
real/div-free constraints、weak gradient、energy inequality 或 nonlinear PDE。C203 完成 coordinate
topology bridge，C204 以兩層 Hölder 關掉 coordinate-product map/convergence gate，C205 再完成
scalar outer-`L¹` restriction laws、product commutation 與 product `L¹_loc` compatible carrier。
physical representation／test-function weak equation limit 仍在其後。

### 1.62 C201：compatible local classes 的 projective-limit-style carrier

C201 將 C200 的 restriction identities 收成 complex submodule

```text
compatibleT3ForwardExhaustionL2Submodule t₀ ≤
  (m : ℕ) → CurrentT3CompactIntervalL2 t₀ (t₀+m),
CurrentT3ForwardL2Loc t₀ := compatibleT3ForwardExhaustionL2Submodule t₀.
```

每個 window evaluation 是 continuous complex-linear projection；submodule membership 精確記錄
所有 `m≤n` 的 nested restriction identity。每個 C181 actual Galerkin cutoff 都由 C200 的 exact
commutation 定理成為 carrier 中的一點。C199–C200 的一條共同 `StrictMono φ` 因而升級為

```text
Tendsto (fun k ↦ fullForwardL2Loc (φ k)) atTop (𝓝 U)
```

在 subtype/product topology 中的真 convergence。這是 compatible quotient classes 的正式
projective-limit-style 載體，不是 global measurable function quotient，也沒有 single global
forward-ray `L²` norm 或 chosen representative；`m=0` 仍是 zero-measure coordinate。

### 1.63 C202：coordinate spacetime energy 與 finite-window norm bridge

C202 將 inner carrier 的每個 coordinate projection

```text
CurrentT3ComplexVectorL2 →L[ℂ] Lp ℂ 2 normalizedT3Haar
```

用 `compLpL` 提升到每個 compact-time outer `L²` carrier，並證其 a.e. action 確實是
`t ↦ F t i`。對任意 outer quotient class（不只 continuous/Galerkin representatives）證

```text
∑ i : Fin 3, ‖coord_i F‖²
  = ∫ currentT3VectorL2Energy (F t) dt,
‖F‖² ≤ ∑ i : Fin 3, ‖coord_i F‖² ≤ 3 * ‖F‖².
```

因此既有 Pi/sup fiber norm 與三座標 displayed spacetime energy 有 squared-norm 常數 `1,3` 的
定量比較，後續可在不偷換 norm 的情況下搬運 strong convergence 與能量估計。這不是 isometry，
也沒有建立 canonical `L²([a,b]×T³;ℂ³)` joint-product carrier、Fubini equivalence 或 global
representative；PDE limit 仍需另外證明。

### 1.64 C203：forward local carrier 的 scalar-coordinate topological embedding

C203 先對任意 source filter（不只 sequences）證一個 finite-window family 在 vector-valued
iterated `L²` carrier 中收斂，若且唯若三個 spatial-coordinate scalar quotient classes 都收斂。
反向使用 C202 的 lower norm comparison、有限和、平方根連續性與 squeeze，不是從 coordinate
maps 的 continuity 倒推。再定義

```text
CurrentT3ForwardCoordinateExhaustionL2 t₀ :=
  (m : ℕ) → (i : Fin 3) → Lp_time (Lp_space ℂ 2) 2
```

並證 `currentT3ForwardL2LocCoordinates` 是 injective `IsEmbedding`。在 `ν>0` 時，C201 的同一
limit `U` 與同一 `StrictMono φ` 同時在 compatible source carrier 收斂，並在 bundled-coordinate
product 收斂到 `coordinates U`。ambient product 本身允許跨視窗不相容的系統；C203 沒有證 surjective、
image characterization、isometry、joint-product/Fubini identification、global representative、
nonlinear product convergence 或 weak PDE。乘法／收斂缺口已由 C204 關掉，cross-window
compatibility 與 `L¹_loc` subcarrier 再由 C205 關掉；weak-PDE passage 仍缺。

### 1.65 C204：兩層 Hölder 與 forward coordinate-product convergence

C204 定義 spatial `L²_x × L²_x → L¹_x` 與 outer-time
`L²_t(L²_x) × L²_t(L²_x) → L¹_t(L¹_x)` curried bilinear maps，核證兩層各自的 a.e. action、
unit-constant product-norm bounds 與 `[0,1]` constant-one nonzero witness。它將每個 window 的九個
ordered products `(i,j)` 包成

```text
CurrentT3ForwardCoordinateProductsL1 t₀ :=
  (m : ℕ) → (i j : Fin 3) → Lp_time (Lp_space ℂ 1) 1
```

並對任意 `{α}` 與 `l : Filter α` 證 local-`L²` convergence 推出三層 `(m,i,j)` product
convergence。在 `ν>0` 時，actual-family theorem 只拆解 C203 一次，保留同一 `U` 與同一
`StrictMono φ`，沒有重抽 subsequence。target 仍是 unrestricted iterated quotient-product：沒有
Fubini/joint `L¹`、cross-window compatibility、product `L¹_loc`、representative、intrinsic
tensor/divergence/convection、weak PDE、trace 或 energy inequality。outer a.e.-in-time 與 inner
a.e.-in-space 公式保持分開，沒有被 flatten 成 joint a.e. representative。

### 1.66 C205：outer-time restriction compatibility 與 product `L¹_loc` carrier

C205 對任意 complex normed value space 與 `p≥1` 構造 norm-nonincreasing compact-window
outer-`Lp` restriction，證明 outer-time a.e. composition formula、constant preservation，以及
identity／transitivity。scalar outer `L²`／`L¹` specializations 分別與 C203 coordinate extraction
及 C204 two-level product commute。所有 `(m,i,j)` restriction identities 被收進 complex
submodule

```text
CurrentT3ForwardCoordinateProductsL1Loc t₀.
```

每個 C201-compatible velocity 的 products 與每個 actual Galerkin cutoff 都是其中的顯式點；
constant-one compatible `L²` source 映到 `m=1` 非零的 constant-one product point。任意-filter
source convergence 可提升到 product subtype topology；在 `ν>0` 時，actual theorem 沿用 C203
同一個 `U,φ`，沒有重抽 subsequence。

restriction 只作用於 outer time，inner spatial quotient 保持 opaque；這不是 joint/Fubini `L¹`
或 global representative。ambient compatible submodule 也未被證明恰等於 quadratic image，沒有
single global norm、image characterization、intrinsic tensor/divergence/convection、test-function
PDE、trace 或 energy inequality。C206 已直接在 iterated carrier 上完成第一層 bounded-test
pairing，避開昂貴的 global-representative bridge。

### 1.67 C206：iterated `L¹` bounded-test pairing 與 scalar convergence

C206 定義 nested bounded-continuous tests

```text
CurrentT3ScalarBoundedTest := T3 →ᵇ ℂ,
CurrentT3CompactIntervalL1Test a b := Icc a b →ᵇ CurrentT3ScalarBoundedTest.
```

先用 mathlib `lpPairing μ ∞ 1` 建 `L∞_x×L¹_x→ℂ`，再於 outer time 重複一次，得到

```text
compactIntervalIteratedL1TestPairing a b :
  Test(a,b) →L[ℂ] L¹_t(L¹_x) →L[ℂ] ℂ.
```

它核證 literal nested formula

```text
∫ t, ∫ x, Ψ(t)(x) * F(t)(x) dHaar dx dt
```

（先 space、後 time），以及 `‖pair Ψ F‖≤‖Ψ‖‖F‖` 與 curried operator norm `≤1`。在 unit
window 上 constant-one test／data 精確配成 `1`；同一計算也在 C205 compatible constant-one
carrier 的 `m=1,i=j=0` functional 上精確等於 `1`，因此不是 zero-measure 空洞。

每個固定 `(m,i,j,Ψ)` 都給 C205 carrier 到 `ℂ` 的 CLM；任意-filter carrier convergence 因而
推出 scalar pairing convergence。family consumer 只接受既有同一 `U,φ` 的 C205 convergence，
不重抽 subsequence。這仍只是 product-subspace convergence 的 continuous image：test 沒有
derivative、density、smoothness、compact support、cross-window extension 或 integration by parts；
pairing 是無 conjugation 的 complex bilinear multiplication，不是 joint/Fubini integral、intrinsic
tensor/divergence/convection 或 weak PDE。C207 已完成 finite-Fourier derivative tests 與九項
pairing finite sum，但刻意不把 fixed-cutoff Galerkin weak identity 偷塞進同一磚。

### 1.68 C207：finite-Fourier gradient tests 與九項 tensor pairing

C207 將 C179 的 finite-Fourier multiplier derivative

```text
finiteFourierCoordinateDerivativeT3 j c q i
```

封裝成 C206 可消費的 spatial bounded-continuous test，證其 pullback 到 cover 後精確等於第 `j`
方向對第 `i` component 的 Euclidean directional derivative，並以 transverse unit coefficient 給出
非零 derivative-test witness。對 bounded-continuous time envelope `η`，它再建立 separated test
`η(t) ∂ⱼϕᵢ(x)`。

九個 ordered product coordinates 被組成一個 tensor-test CLM，其 literal formula為

```text
Σᵢ Σⱼ ∫ t, ∫ x, Ψᵢⱼ(t)(x) * Pᵢⱼ(t)(x) dHaar dx dt.
```

它具有逐項 norm bound，且只在 `(0,0)` 放 constant one 的 tensor test 會在 C205 的 positive-window
constant-one carrier 上精確取值 `1`，因此 functional 非空洞。specialization `Ψᵢⱼ=η∂ⱼϕᵢ`
給出 unsigned quadratic-gradient functional；任意-filter carrier convergence 以及 `ν>0` actual
family 的同一 `U,φ` convergence 都經此固定 CLM 送到 scalar convergence，沒有重抽 subsequence。

這不是 convection 或 weak Navier--Stokes identity：pairing 無 conjugation，尚未解決 C153
Hermitian coefficient pairing與 C206 bilinear field pairing之間的 frequency-reflection convention；
也沒有 cross-Parseval、cross-gradient、three-monomial/convolution bridge、integration by parts、
可微 time envelope、endpoint/FTC、Stokes/Leray/pressure、joint/Fubini carrier、smooth/dense/
divergence-free test class或 limiting PDE。C208 現已完成 cross-Parseval／cross-gradient／Stokes
這個低成本 coefficient/field 子包；C209 已再完成 triple-monomial selection與兩側 zero-sum
expansions；C210 已組 signed static RHS，C211 已組 fixed-cutoff separated spacetime weak
identity；C212 已組 limiting finite-Fourier carrier equation。general test closure與 physical
representation仍未完成，但不是已認證的 mathlib wall。

### 1.69 C208：finite-Fourier Hermitian cross-Parseval 與 cross-gradient

C208 把 C178/C179 的 self-energy identities 升為兩個不同 finite coefficient families `d,c`
的 cross identities。對任意同時包含兩邊 support 的 finite set `s`，兩個 syntheses 先被重寫在
同一 transported orthonormal monomial family 上，得到

```text
Σᵢ ∫ₓ conj(ϕ_dᵢ) ϕ_cᵢ = Σₙ∈s ⟪dₙ,cₙ⟫,
ΣⱼΣᵢ ∫ₓ conj(∂ⱼϕ_dᵢ) ∂ⱼϕ_cᵢ = Σₙ∈s |n|² ⟪dₙ,cₙ⟫.
```

兩式都是 normalized-Haar literal integrals，第二式使用 C179 multiplier derivatives 的 actual
`L²` representatives。Stokes cross pairing另精確等於 `-ν` 乘 weighted coefficient cross sum。
C147 transverse unit family與其 `Complex.I` scalar multiple已證彼此不等，而 cross pairing及
cross-gradient pairing均精確為 `Complex.I`，所以不是 self-energy disguise或 zero-only theorem。

這裡 first slot 有 conjugation，是 Hermitian convention；C206/C207 則是無 conjugation 的
complex-bilinear physical product。對 arbitrary complex tests，兩者不可直接等同；例如兩族都只
支撐同一非零正頻率時，Hermitian pairing非零，但 bilinear field integral落在雙頻率而為零。
C208 未證 conjugate-symmetry/frequency-reflection bridge、triple-monomial integral、convolution-
to-physical-product、Leray removal、signed convection/static RHS、time/endpoint/FTC、weak identity
或 limiting PDE。下一節 C209 已獨立完成 monomial與 reflected coefficient expansions；C210
則已完成 complex-bilinear signed identity、Leray removal與 static RHS，但仍沒有 Hermitian bridge。

### 1.70 C209：triple-monomial selection 與 reflected convection expansion

C209 在 repository 的 actual normalized Haar torus上證

```text
χₚ χ_q = χ_(p+q),
∫ χ_n = if n = 0 then 1 else 0,
∫ χₚ χ_q χ_r = if p + q + r = 0 then 1 else 0.
```

三個零頻率的 literal integral另被算成 `1`。對任意 finite coefficient families `a,b,d` 與
components `i,j`，因此得到 `∫aᵢbⱼ∂ⱼdᵢ` 的 actual finite zero-sum triple expansion。另一個
theorem則把 `Σ_r B(d_r,N(c)_{-r})` 展開為同樣帶 `p+q+r=0` constraint 的 reflected
Galerkin convection sum。

兩式目前只被**分別展開**，尚未彼此識別。由 zero-sum relation得到正確 global minus sign仍須
交換 `p,q` 並消耗 state/test transversality；之後才可 sum over `i,j`、移除 transverse-test 下的
Leray projector並組 static RHS。C209 也沒有 time envelope、endpoint/FTC、fixed-cutoff weak
identity、limiting PDE、initial trace、energy inequality、Leray--Hopf或 Clay result。

### 1.71 C210：signed reflected convection 與 static Galerkin RHS

C210 在 C209 的 actual finite sums上完成 `p↔q` reindex。對 state `c` 只要求
`fourierWaveDot q (c q)=0` 於 `c.support`，由 `p+q+r=0` 得正確 global minus sign：

```text
Σ_i Σ_j ∫ u_c,i u_c,j ∂_j d_i
  = - Σ_r B(d_r, finiteGalerkinConvectionMode(c.support,c,-r)).
```

這是 C207/C209 的 complex-bilinear pairing；沒有 conjugation，也不需要 reality。C210 另證
包含 state support 的 cutoff不改變 convolution mode；test coefficient transverse於 `r` 時，
可移除作用在 `-r` mode的 Leray projector；reflected Stokes pairing則是
`(-ν)Σ_r |r|²B(d_r,c(-r))`。在兩邊 support都落入 negation-closed cutoff時，合成

```text
Σ_r B(d_r, finiteGalerkinRHS(ν,s,c)(-r))
  = (-ν) Σ_r |r|² B(d_r,c(-r))
    + Σ_i Σ_j ∫ u_c,i u_c,j ∂_j d_i.
```

non-vacuity gate使用 `s={-k,0,k}`：同一 theorem statement同時證兩個 support containment、
cutoff取負封閉、state/test transversality，且 `ν=0` 的 RHS pairing精確為 `-Complex.I`。
第一版只用 `s={0,k}` 的 raw witness曾被 reviewer判定不能實例化 headline；正式版已把這個
admissibility blocker機器化修掉。

C210 仍是 finite Fourier、static、reflected identity，不是 C208 Hermitian bridge，也不是 time
integrated weak equation。它沒有 time envelope、product rule、endpoint／FTC、fixed-cutoff
spacetime identity、limiting PDE、initial trace、energy inequality、Leray--Hopf或 Clay result。

### 1.72 C211：fixed-cutoff separated Galerkin spacetime identity

C211 把 C210 的 static formula沿 `alpha : ℝ → CutoffState s` 的 actual Galerkin ODE積分。
對 fixed finite Fourier test `d`，定義 reflected bilinear pairing `G`、frequency-squared pairing
`D` 與 physical product-gradient pairing `Q`：

```text
G(t) = Σ_r B(d_r, cutoffCoeff(s,alpha(t))(-r)),
D(t) = Σ_r |r|² B(d_r, cutoffCoeff(s,alpha(t))(-r)),
Q(t) = Σ_i Σ_j ∫ u_i(t,x)u_j(t,x)∂_j d_i(x).
```

若 cutoff對取負封閉、test support落在 cutoff內、state/test各自 transverse，且 scalar envelope
`eta` 有指定連續導數 `eta'`，則 C210 與 product rule給

```text
(eta G)' = eta' G + eta ((-ν)D + Q).
```

因此對 `a≤b`，exact weak-sign form是

```text
∫_a^b (-eta' G + ν eta D - eta Q)
  = eta(a)G(a) - eta(b)G(b).
```

`eta(b)=0` 的 corollary保留正號 initial endpoint。完整 integrand的 interval integrability由
ODE／RHS continuity與 `eta'` 的 `ContinuousOn`自動供給，不是假設黑箱。另有 exact
`compactIntervalVolume` subtype-integral bridge，與 C207 的 iterated spacetime convention一致。

C171 applicability theorem輸出同一 `alpha` 的 initial value、forward ODE、all-time reality、
transversality與 spacetime identity。C181 structure本身未保存 constraints；C211 用 C175 actual
model與 `ForwardCubeFieldFamily.unique` 在 forward ray搬運 reality/transversality，並直接提供
stored-family ordered-interval與 compact-measure版本，讓 C212可消費同一 compactness family。

誠實邊界：這仍是 fixed finite cutoff、complex-bilinear `-r` reflection，以及 separated
`eta(t)d(x)` test。C211 本身尚未把 identity沿 C205 的同一 subsequence取極限，沒有 arbitrary
smooth-test density、global representative、initial trace、limiting energy inequality、
Leray--Hopf、regularity、blow-up exclusion或 Clay result。下一節 C212完成前述 fixed-test
cutoff-limit passage，但不補其餘邊界。

### 1.73 C212：limiting finite-Fourier weak identity

C212 把 C211 的三項拆成可沿 C205同一 subsequence傳遞的 carrier functionals。首先對 finite
Fourier test `d` 建立 unconjugated complex-bilinear spatial pairing，並證 exact reflected
Parseval公式

```text
Σ_i ∫ d_i(x)u_c,i(x) = Σ_r B(d_r,c(-r)).
```

`finiteStokesApply (-1) d` 的 coefficient是 `|r|²d_r`，所以 compact-window linear CLM在 actual
Galerkin field上精確等於 `∫(-eta'G+ν eta D)`。另一方面，C207 compatible product carrier上的
finite-Fourier gradient functional在 actual coordinate products上精確等於 `∫eta Q`；證明只
展開兩層 a.e. representatives與有限 `i,j` sums，沒有 Fubini假設。

當 `eta(t₀+m)=0`、`d` transverse且 support已進入 cube時，C211與 initial Leray removal給

```text
LinearWeak(U_N) - QuadraticGradient(P_N)
  = eta(t₀) InitialReflectedPair(u,d).
```

對 fixed `d`，任何 `StrictMono phi` 都 eventually包含其 finite support。C205同一 `phi` 的
velocity `L²_loc` convergence與 compatible product `L¹_loc` convergence分別經兩個 continuous
functionals傳成 scalar limits；再由 complex Hausdorff uniqueness識別上述常值極限。positive
viscosity headline一次選出同一 `U,phi`，其後才量化所有 integer windows、finite transverse
tests與 final-zero differentiable scalar envelopes，沒有重抽 subsequence。

誠實邊界：test仍是 separated scalar-time × finite-Fourier-space；pairing沒有 conjugation且固定
反射在 `-r`。local `L²`是 a.e. quotient，C212因此不寫 `U(t₀)`或 `U(t₀+m)`；右端是 supplied
ambient initial datum的 Fourier pairing。`m=0` 是 zero-measure window。尚無 finite sums之外的
general smooth-test closure、global/physical representative、pointwise initial trace、limiting
energy inequality、Leray--Hopf、regularity或 Clay result。下一節 C213已完成 termwise-final-zero
finite presentation package，但不改變其餘邊界。

### 1.74 C213：termwise-final-zero finite separated sums

C213 定義 `AdmissibleSeparatedFiniteFourierTest t₀ m`，把單項的 `eta`、`eta'`、finite spatial
coefficient、derivative、derivative continuity、final-zero與 transversality集中成一個可消費
物件。每項產生 velocity `L²_loc` carrier與 compatible product `L¹_loc` carrier上的 CLM；任意
finite type index再給兩個 genuine CLM sums及 ambient initial pairing sum。

compact-window pairing有 literal space-then-time iterated-integral公式。外層 finite sum的積分
交換只依靠 Holder所給每項 integrability與 `integral_finsetSum`；沒有交換 time/space integrals，
沒有 joint-product/Fubini equivalence或 chosen jointly measurable representative。

finite-cutoff theorem要求一個 cube同時容納所有 supports。limit theorem對 finite index使用
`Filter.eventually_all`取得共同 cutoff stage，再讓 summed CLMs沿 C205同一 `U,phi`傳極限；
positive-viscosity headline把同一 `∃ U,phi` 放在所有 `m,n, Fin n → test`之前。

誠實邊界：這是 presentation-level algebraic package，邏輯不強於逐項 C212。每個 summand
個別 final-zero；不同 decompositions沒有 quotient，沒有 test topology、uniform-in-test
convergence或 closure。empty family與 `m=0`只給 vacuous zero identity。下一節 C214 已完成
真正較強的 aggregate endpoint cancellation：只要求
`Σ_k eta_k(T) • d_k = 0`，允許各項 endpoint非零。

### 1.75 C214：aggregate final-endpoint cancellation

C214 去掉 C213 的逐項 terminal-zero field，保留有限族的 literal aggregate
coefficient

```text
Σ_k eta_k(t₀+m) • d_k = 0.
```

終點 reflected pairing 先被封裝成 `FiniteFourierVelocity` 上的 complex-linear map，
再用 `Finsupp.lsum` 與 finite-sum linearity將整個 terminal contribution 消去。因此
finite-cutoff theorem 可直接從 C211 的雙 endpoint identity 導出；limiting theorem 再沿
C212–C213 的同一 `U,phi` 與共同 cutoff stage 傳遞，不需在 limit `L²` class 上
評估 endpoint。

這仍是 literal finite decomposition，沒有把不同 spacetime-test presentations 取 quotient，
也沒有 test topology、closure 或 density。`m=0` 時初、終 coefficient 相同，aggregate
cancellation 連初值右邊也一併消去，所得仍是 zero-measure 上的 vacuous identity。

### 1.76 C215：common compactly supported time bump

對 `0 < m`，C215 用 mathlib `ContDiffBump` 在 `t₀+m/2` 構造共用時間 bump，
inner/outer radius 取 `m/8` 與 `m/4`。已正式證明它非零、無限可微、
`HasCompactSupport`，support 包含於 `Ioo t₀ (t₀+m)`，並在兩 endpoint 為零。
以任意實權重乘同一 bump，再搭配任意 finite transverse complex Fourier
directions，自動生成 C214 可消費的有限族；complex scalar 可吸收到 spatial
coefficient，因此實權重已足夠。

這只構造一個明示非平凡時間族。它沒有證 finite Fourier tests 在任何
intrinsic smooth spacetime-test topology 中稠密，`m=0` 也沒有 interior 可放這個 bump。

### 1.77 C216：algebraic weak-residual consumer jet

C216 把 C214 的消費結果包成四個 ambient slots：velocity-carrier CLM、
product-carrier CLM、已在 fixed datum `u` 評估的 initial scalar，以及 terminal
`FiniteFourierVelocity`。terminal projection 的 kernel 是 zero-final submodule；給定 `U,P` 後，
殘差是 plain linear map

```text
Residual(J) = J.velocity(U) - J.product(P) - J.initial.
```

C214 realizable aggregate jets 在 zero-final 條件下殘差為零。但只把 initial scalar
設為 `1` 的 ambient formal jet 也在 zero-final kernel，其殘差精確為 `-1`；因此
「殘差消去整個 ambient zero-final kernel」是錯的。此 carrier 沒有記錄 window、
smoothness、support 或 time-envelope/derivative 關係，也沒有選取 topology；它是
consumer bookkeeping，不是 intrinsic physical test space。

### 1.78 C217：realizable zero-final residual-jet span

C217 只收集所有 `m,n` 與 `Fin n` presentations 所生成的 literal realizable
zero-final jets，再取其 complex `Submodule.span`。已證這個 span 落在 ambient
zero-final kernel，並被 C214 選定的同一 `U,phi` residual 消去。這個對象依賴
`ν` 與 fixed initial datum `u`，因為 consumer slots 已把 viscosity 與 initial evaluation
編入。

`Submodule.span` 只是有限代數閉包，不是 topological closure、density 或
uniform-in-test limit；也沒有證這個 span 等於 ambient zero-final kernel。C218 後續只在
特定 constant datum、initial time 與 window 給出一個 nonzero generator witness，不是任意
parameters 的非平凡性。

### 1.79 C218：finite Fourier transverse/reality carriers

C218 將 modewise `fourierWaveDot = 0` 寫成 complex-linear map 的 kernel，得到 complex
transverse submodule；conjugate symmetry 則封裝成 real submodule，再以
`restrictScalars` 取得誠實的 real transverse intersection。顯式 `Complex.I` 反例證明
reality 不在任意 complex scaling 下保持，所以不能偽裝成 complex subspace。

同時已加入 support/all-frequency transversality 等價、finite Leray wrappers、明示 nonzero
real-transverse witness，以及直接產生 C215 common-bump tests 的 consumer wrappers。這些仍只是
finite coefficient carriers；沒有將它們辨識為 intrinsic physical vector fields，也沒有
norm completion、topology 或 density theorem。

### 1.80 C219：weak-residual consumer density feasibility gate

C219 在 zero-final 後忘掉 terminal coefficient，只保留 velocity CLM、product CLM 與
initial scalar 三個 consumer slots。兩個 CLM slots 使用 mathlib 在 non-seminormed local
domains 上的 bounded-convergence topology（對 von-Neumann-bounded subsets 一致收斂），不是
operator-norm topology；scalar 與 product 使用通常 topology。fixed `U,P` 的 residual 藉
`continuous_eval_const` 成為 genuine continuous linear map。

C217 span 的三槽代數投影之 set closure 包含於這個 continuous residual 的 closed
kernel。unit-initial consumer 的 residual 為 `-1`，因此該 closure 不可能是 whole
ambient three-slot consumer。投影本身只作 algebraic map 使用，沒有宣稱 continuous，
證明也沒有交換 closure 與 image。

最重要的誠實邊界是：C219 **只否定 whole ambient consumer 的 naive density**。
它沒有否定 residual kernel 內的 density，也沒有否定未來 intrinsic physical-test
carrier 中的 density；這兩者才是正確的下一候選目標。目前仍沒有 physical-test
topology、positive density theorem、endpoint trace、energy inequality 或 Leray--Hopf weak solution。

**歷史 C220–C259 pipeline 已把上述負向 gate接到 canonical LF time-test carrier、literal
realizable provenance、finite-family identities、complete algebraic tensor consumer、必要
image constraints、faithful quotients、全部 velocity/product-gradient/initial/complete consumer
的 cross-window stability、window-free global algebraic tensor、exact realizable image、selected
residual factorization及單向 global image ≤ all-window image；contact code/receipt checkpoint
為 `8e89a6c`／`019842c`。C260–C262 已把單向 inclusion搬到 faithful quotient並證 residual
naturality；C263–C271 已加入 weighted-`lp 1` transverse coefficient／absolute synthesis／LF
continuous-field bridge；C272–C283 再加入 closed coefficient reality／real-transverse intersection、
reality-preserving symbols、native-real coordinate-field LF transport與一個 displayed in-range witness。
**兩個舊 tensor carriers與 C271 composite仍是 algebraic；C259–C262沒有 reverse inclusion或
image equality，C272–C283 仍沒有 LF completeness、intrinsic tangent-field/divergence、physical
representation或一般 density，且 C283 的不同 transport-range theorem不補 C271 composite gap。**

## 2. 正式目標要分層，不可把終點當工程 ticket

### 已知理論層（可形式化的工程目標）

1. 週期三維域上的光滑/強解定義與 pressure gauge。
2. 對流項能量消去與基本 `L²` energy identity/inequality。
3. 有限 Fourier-mode Galerkin 系統及其有限維全域解。
4. 局部強解、最大存在時間與 continuation alternative。
5. 小資料全域解。
6. Leray–Hopf 全域弱解與能量不等式。
7. weak–strong uniqueness 與條件正則性準則。

### 未解核心（不可預先宣告可完成）

對任意大、光滑、divergence-free 三維初值，要嘛證明其解永遠保持光滑，要嘛構造有限時間
失去正則性的合格初值。這一步需要新的全域高階先驗估計或經認證的奇異解構造；它不是缺少
幾個 Lean lemma，也不會由 Turing-completeness、特殊 steady field 或 C141 的顯式解推出。

最終介面應只先定義，而不可把任一分支當假設偷塞進去：

```text
GlobalRegularityPeriodic3D ∨ FiniteTimeBreakdownPeriodic3D
```

## 3. Repository architecture

建議建立獨立 `navier_stokes_lean`，理由如下：

- 真 PDE 主線不應繼承 M7 的未詮釋 signature 或 Turing-machine dependency graph。
- 可暫時單向依賴 `contact_geometry_lean` 的 flat operators；成熟後再把一般分析 lemma 上游化或
  搬到較小的 vector-calculus dependency。
- `fluid_turing_lean` 保留 computability 與抽象 realization 工作；M61 是誠信邊界。
- `contact_geometry_lean` 保留接觸幾何與 flat-calculus 基建；C141–C219 是跨入 PDE/週期分析的 anchors，
  不在該庫內堆完整 Sobolev/Galerkin 生態。

所有新模組維持共同 gate：零 `sorry`、零自訂 axiom、header 明列 honest scope、定義需有
非空洞 witness 或反例測試。

## 4. 分期路線與驗收條件

| Phase | 建議模組 | 內容 | 驗收條件 |
| --- | --- | --- | --- |
| NS001 | `ClassicalResidual` | **已由 C142 完成介面層：**forward interval、初值 trace、真 momentum residual、pressure gauge | 常場與 C141 型衰減場通過；方程字面含 div-free、`ν>0`、初值 |
| NS010 | `PeriodicT3` | **部分完成：**C143 carrier/Haar、C144–C145 scalar/vector Parseval、C146 lifted multipliers、C147 divergence、C148 finite reality、C178 common quotient-`T³` synthesis、C179 multiplier/cover derivative、C182 continuous linear cutoff reconstruction；仍欠 arbitrary fields 的 intrinsic quotient calculus 與 completed mean-zero/Sobolev subspace | finite reconstruction/導數與代表元相容；一般 intrinsic API 尚未完成 |
| NS020 | `EnergyCancellation` | **finite coefficient 版由 C150–C151 完成，C157–C181 已接到 arbitrary-real-data 的 unique forward-global fixed-cutoff solutions、common field energy/gradient bounds、initial tails 與 cutoff-indexed selection：**pressure 消去、viscous dissipation、convection cancellation、pointwise derivative、exact integrated identity、C178 Parseval reconstruction、C179 gradient identity，以及 C180–C181 的 field-level spacetime bound/family；仍欠一般 smooth-field integration by parts 與真 PDE energy identity/inequality | 假設最小且真被 proof 消耗；有非零 Fourier witness |
| NS030 | `FourierLeray` | **finite coefficient core 進一步完成：**C149 modewise/finite Leray、C150 Stokes multiplier、C152 reality preservation、C173 real-`L²` coefficient reality、C174 exact Pythagoras/contraction、C177 summable projected total/tails、C178 finite-field synthesis；仍欠 completed-space bounded/self-adjoint extension 與完整 commutation package | finite projector 與 common finite-field carrier 已清楚；completed-space Leray 物件仍未建 |
| NS040 | `Galerkin` | **C153–C283 已完成 fixed-cutoff core、compatible local compactness/products、signed spacetime identity、同一 subsequence limit、canonical LF zero-final tests、finite-family identities、consumer obstruction、complete algebraic tensor consumer、faithful fixed/global quotient、全部三槽的 window stability、canonical global tensor/image/quotient/residual package，以及 real weighted-coefficient LF field bridge：**C260–C262 只把 C259 的單向 inclusion傳到 quotient/residual square；C263–C283 建 coefficient reality、native-real continuous/LF tests與 symbol cancellation | fixed-cutoff、compactness、products與 algebraic tensor-test tickets complete；下一 gate 是 LF/intrinsic/completed physical-test結構與正確 density，不是未證的 reverse/equality、composite-range witness或 whole ambient/residual kernel density |
| NS050 | `TorusSobolev` | **finite-field/consumer 第一層由 C178–C283 完成：**common synthesis/derivatives、homogeneous gradient bound、negative carrier、compactness、iterated/projective velocity/product carriers、finite-Fourier identities、canonical LF time carrier、complete algebraic tensor consumer、cross-window stability、global faithful quotient/residual naturality，以及 weighted-`lp 1` coefficient reality、real transversality與 native-real continuous/LF synthesis；仍欠 LF completeness、intrinsic/completed Sobolev與 physical-test topology、intrinsic tangent-field/divergence、canonical physical joint-vector/product representation及 global representative | 不把 complete coefficient subtype冒充 complete LF或 physical field space，不把 coefficient-symbol cancellation冒充 intrinsic divergence-free theorem，也不把單向 inclusion說成 equality或 density |
| NS060 | `LocalStrong` | contraction 或 Galerkin local strong solution | existence、uniqueness、continuous dependence、maximal time |
| NS070 | `LerayHopf` | C198–C219 在 `ν>0` 時供 fixed-window compactness、共同 subsequence、local velocity/product carriers、complex-bilinear fixed/limiting identities、aggregate cancellation 與可審核的 consumer residual kernel；仍欠 intrinsic adequate smooth tests、physical representation、weak gradient、pointwise initial trace與 energy inequality | C219 只排除 whole ambient consumer 的 naive density；不把 residual-consumer package說成 Leray--Hopf weak solution，更不假裝三維唯一 |
| NS080 | `RegularityCriteria` | weak–strong uniqueness、Prodi–Serrin/BKM 類準則 | 條件範數與時間端點精確；不把 conditional 變 unconditional |
| NS090 | `ProblemStatement` | periodic/`ℝ³` Clay-style statement 與 breakdown alternative | 僅定義與邏輯關係；沒有未證終局 theorem |

## 5. 下一輪的三個具體工作包

### WP-A：NS001 真方程介面（已完成）

- C142 從 C141 抽出 `IsFlatNSClassicalSolutionOn I ν u p u₀`。
- 使用 forward order-convex domain 與 `HasDerivWithinAt`；若要求 open subset 同時含 0 且
  包含於 `[0,∞)`，規格反而不一致。
- constant solution、C141 restricted solution、pressure gauge 已通過。
- singleton within-derivative 攻擊已實際重現並封堵；residual 不接受 domain 外時間。

### WP-B：T³ calculus census/probes（已完成盤點，bridge 已部分落地）

- 五個 pinned compile probes 驗證 `UnitAddTorus (Fin 3)` Haar/Fourier/Parseval、現有 `T3`
  的保測度橋、單變量 Fourier integration-by-parts、C124 character multiplier 接線，以及
  C143 energy identity；C143 已把 Haar/measure-preserving/L²-isometry bridge 正式入庫，C144
  已把 scalar coefficient/integral/Parseval bridge 正式入庫，C145–C211 再加入三分量 Parseval、
  lifted multiplier、有限支撐散度/實值/Leray/Stokes/pressure、對流抵消公式與 local Galerkin
  solution package。
- `UnitAddTorus.mFourier`、`mFourierBasis`、`mFourierCoeff`、
  `hasSum_prod_mFourierCoeff`、`hasSum_sq_mFourierCoeff` 與
  `mFourierCoeff_eq_integral` 均為 `PROBE-PROVED`。
- pinned mathlib 沒有已定位的 arbitrary quotient-torus functions 上的 general intrinsic
  multivariate derivative API；此項仍是 `UNASSESSED`，不宣稱不存在。C179 只在 finite
  Fourier class 上以 multiplier 定義 derivative field，並證其 cover pullback 是 actual
  Euclidean coordinate derivative。C132 的 `rep3` 不連續，禁止拿來微分。

### WP-C：一般有限頻譜能量抵消與 finite-field transport（已完成）

- C143 已完成**一個顯式 mode**的可積性與精確能量 ODE；它不是本工作包所指的一般
  energy cancellation。
- C150 已分開證 pressure orthogonality 與 viscous dissipation；C151 已在任意取負封閉 cutoff 上
  證 exact convection cancellation，且假設逐項被 proof 消耗。
- C153–C283 已把 Leray/Stokes/convection 組成有限維 ODE，證任意 initial time 的 unique
  forward-global admissible original solution、pointwise/integrated energy laws，以及由同一 arbitrary
  real vector `L²` datum 自動產生的 coherent projected initial states、common evolved energy-state
  bounds 與 positive-viscosity integrated-dissipation bound。C165–C168 的 compact-support
  `UniformTime` + energy bump 路線已正式入庫並完成 de-truncation；C178–C180 另將其
  coefficient energy/dissipation 精確辨識為共同 field `L²`/homogeneous-gradient 量；C181 再把
  逐 cube curves 一次選成 indexed family；C182 再證每個 reconstructed member 在 common
  carrier 上 forward time-continuous；C183–C259 另完成 common coefficient `H⁻³` carrier、
  cutoff-independent projected-convection/full RHS bounds、actual derivative transport、integrated
  RHS-energy estimate、Banach FTC、squared trajectory increment estimate 與 whole-forward-ray
  uniform equicontinuity，以及 integrated Fourier tail、fixed-low-mode common-field equicontinuity、
  static compact closure；在 `ν>0` 時再得到 fixed-low-mode Ascoli、iterated spacetime carrier、
  fixed-window compactness、共同 exhaustion subsequence、compatible local projective carrier、
  coordinate spacetime norm bridge、scalar-coordinate embedding、同一 `U,φ` 上的 nine-product
  iterated-`L¹` convergence、outer-time cross-window compatibility／product `L¹_loc` subtype，
  以及 fixed bounded-test scalar convergence，不再只是 probe。抽象 two-level Hölder、generic
  restriction、pairing 與 arbitrary-filter convergence theorems 本身不需 viscosity 假設。C207
  另將 finite-Fourier spatial derivatives 組成九項 unsigned quadratic-gradient functional 並證
  same-subsequence scalar convergence；C208 再補兩族 finite fields 的 Hermitian cross-Parseval、
  cross-gradient與 Stokes cross pairing，C209 補 triple selection及 physical/reflected coefficient
  expansions，C210 再接成 signed convection、Leray removal與 static RHS；C211 加入 scalar time
  envelope、endpoint／FTC與 actual/stored-family fixed-cutoff spacetime weak identity；C212–C259 已續作
  cutoff-limit identity、finite/aggregate tests、compact-time bump、residual-jet span、
  transverse/reality carriers、ambient/residual-kernel obstruction、canonical LF zero-final tests、
  finite-family weak identities、complete algebraic tensor consumer、whole-range realizability與
  necessary closed image constraints、faithful fixed/global quotients、all-window image/residual
  factorization、compact-support tail control、zero-extension integration、全部 consumer slots 的
  cross-window stability、canonical global-time/spatial bilinear map與 algebraic tensor lift、whole-range
  realizability、faithful quotient、selected residual factorization，以及 C259 單向
  global image ≤ all-window image。C260–C262 再建立單向 quotient embedding與 residual naturality；
  C263–C271 建立 weighted-`lp 1` transverse coefficient subtype、absolute/continuous synthesis、
  coefficient-與 continuous-field-valued LF tests及 pure-tensor pointwise公式；C272–C283 再建立
  coefficient reality、closed real-transverse intersection、reality-preserving symbol synthesis、
  native-real coordinate-field LF transport與一個 explicit in-range witness。這仍沒有 reverse
  inclusion、image equality、LF completeness、intrinsic tangent-field/divergence、density或 completed
  physical carrier；C271 explicit witness仍未證為 composite的像，C283處理的是不同 transport map。
- reconstructed finite fields 的 normalized-Haar exact balance 與 spacetime bound 已完成；一般
  smooth periodic integration by parts、limiting PDE energy inequality 與 weak-solution limit 仍未完成。

## 6. 目前 pinned mathlib 的初步 inventory

本機唯讀搜尋與 compile probes 找到：tempered-distribution Sobolev、compact-support Sobolev
inequality、`UnitAddTorus` 多維 Fourier/Parseval、Bochner integration、`Lp` completeness、
Hölder/Fubini、Banach-space Picard–Lindelöf、Gronwall、Banach–Alaoglu 與部分弱緊性。

Pin 的兩個重要陷阱已由 probe 鎖定：`AddCircleMulti` 的 normalized `UnitAddCircle` measure
instance 必須明確重建；`AddCircle (2π)` 的 default `volume` 質量是 `2π`，不能冒充 probability
Haar。C143 已把正確選擇封裝成 `normalizedT3Haar`。

尚未定位到可直接使用的 Leray projector、torus Sobolev Hilbert package、Galerkin NS、
Aubin–Lions/Rellich、heat semigroup 或完整 convolution Young API。這些全部標為
`UNASSESSED`；下一輪用小型 compile probes 決定是 reuse、補 bridge，或新建。

另已定位並正式使用：
`Mathlib/Geometry/Manifold/IntegralCurve/UniformTime.lean` 的
`exists_isMIntegralCurve_of_isMIntegralCurveOn` 可把同一正時間窗上的 local integral curves
拼成 global curve。C165 已將它與 `ContDiff.lipschitzWith_of_hasCompactSupport` 封裝成
「`C¹` 且 compactly supported 的 Banach-space vector field 有全時間 solution」；C166–C211
再完成 energy-dependent truncation、constraint propagation、scaled energy、forward
de-truncation、arbitrary-time uniqueness、integrated balance、nested initial `L²` bridge、automatic
real/Leray admissibility、common integrated dissipation、common quotient-`T³` finite synthesis、
exact field `L²`/homogeneous-gradient identification、field-level spacetime gradient transport，及
common negative carrier 中的 trajectory derivative/time-integration/FTC/increment/equicontinuity
control，加上 common-field integrated high tail、fixed-low-mode equicontinuity、static Rellich
input；在 `ν>0` 時再有 fixed-low-mode compact paths、iterated spacetime carriers、共同 exhaustion
subsequence、compatible local projective carriers、coordinate spacetime norm bridge、
scalar-coordinate embedding、coordinate-product convergence／outer-time compatibility、fixed
bounded-test pairings、finite-Fourier quadratic-gradient pairings，以及 Hermitian cross-duality。

## 6.1 立即施工順序

1. **已完成 C144–C219 的 finite-Galerkin 到 consumer feasibility gate pipeline：**Parseval、
   finite Leray/Stokes/convection algebra、arbitrary-time forward-global ODE、energy/gradient bounds、
   coherent projected initial data、common field reconstruction、negative-space time control、Fourier
   tail；在 `ν>0` 時再有 fixed-low-mode Arzelà--Ascoli、明示 iterated carriers、fixed-window
   compact closure、一條共同 `StrictMono` exhaustion subsequence、所有 nested-window `L²`
   restriction compatibility、projective local carrier、coordinate squared-norm comparison、
   scalar-coordinate topological embedding、九個 ordered products 的 iterated-`L¹` convergence、
   product outer-time restriction compatibility／`L¹_loc` subtype、fixed bounded-test scalar
   convergence、finite-Fourier quadratic-gradient nine-term pairing，以及兩族 field 的 Hermitian
   cross-Parseval／cross-gradient／Stokes duality、triple-monomial selection、physical/reflected
   coefficient signed identity、Leray removal、static RHS，以及 actual/stored-family scalar-envelope
   endpoint／FTC weak identity、同一 `U,φ` 上的 limiting carrier identity及其 finite CLM sums，
   均已 kernel-check。
2. **已完成 C204 two-level Hölder product：**spatial `L²_x × L²_x → L¹_x` 與 outer-time
   `L²_t × L²_t → L¹_t` 已組成明示的 iterated `L¹_t(L¹_x)` map；沿 C203 的同一 `U,φ`
   證每個 `(m,i,j)` product 強收斂，沒有重選 subsequence。這只解 coordinate-product
   convergence，不冒充 joint-product Fubini `L¹` 或弱方程。
3. **已完成 C205 product restriction compatibility：**generic outer-`Lp` restriction 的 norm bound、
   a.e. composition、identity／transitivity，以及 coordinate/product commutation 均已證；所有
   `(m,i,j)` identities 已封裝為 product `L¹_loc` subtype，並沿用同一 `U,φ` 升級 convergence。
   inner/outer quotient 仍分開，沒有 flatten 成 joint a.e. representative。
4. **已完成 C206 iterated bounded-test pairing：**對
   `Icc a b →ᵇ (T3 →ᵇ ℂ)` 建立兩層 `L∞×L¹` CLM、literal nested integral、unit norm bound 與
   raw/carrier exact-one witnesses；C205 carrier convergence 對每個固定 `(m,i,j,Ψ)` 推出 scalar
   convergence。尚無 test restriction/extension、smoothness、derivative、density或 weak PDE。
5. **已完成 C207 finite-Fourier gradient-test pairing：**spatial multiplier derivatives、exact
   cover derivative、bounded-continuous time envelope、九項 tensor CLM、literal nested formula、
   derivative-test／generic-tensor norm/nonzero gates與同一 `U,φ` 的 fixed-functional scalar
   convergence均已 kernel-check；尚無 specialized-functional nonzero theorem、signed convection、
   smooth/dense/divergence-free test space或 weak identity。
6. **已完成 C208 finite-Fourier cross-duality：**arbitrary coefficient pairs 的 Hermitian
   cross-Parseval、cross-gradient、Stokes cross pairing與 distinct nonzero witnesses均已
   kernel-check；尚未接上 C207 bilinear convention。
7. **已完成 C209 triple/reflected expansions：**monomial product、單模態／triple integral、
   arbitrary three-field component expansion與 `d_r` 對 output `-r` 的 bilinear convection sum
   均已正式入庫；兩側只分別展開，沒有冒充 signed equality。
8. **已完成 C210 signed static RHS：**state/test各自 modewise transverse且兩邊 support落入
   negation-closed cutoff時，finite-sum reindex、reflected Leray removal與 signed convection/full
   RHS headline均已 kernel-check；不需要 test conjugate symmetry或 addition closure。
9. **已完成 C211 fixed-cutoff spacetime weak identity：**可微 scalar time envelope、product rule、
   explicit endpoints、FTC、weak-sign ordering、C171 actual curve、stored cube family與 compact-
   measure版本均已 kernel-check；不需要 reality作為 identity本身的假設。
10. **已完成 C212 limiting finite-Fourier weak identity：**linear time/viscous terms消費 local strong
   `L²` convergence，二次項消費 C207 compatible product convergence；finite support eventual進入
   同一 `StrictMono` cubes，initial side保持 ambient datum pairing。沒有 endpoint evaluation。
11. **已完成 C213 finite separated sums：**admissible item、finite CLM sums、literal iterated integral、
   common cutoff/limit與 selected-family headline均已入庫；這仍是 termwise-final-zero presentation，
   不是 quotient test space或 closure。
12. **已完成 C214 aggregate endpoint cancellation：**只假設
   `Σ_k eta_k(t₀+m) • d_k = 0`，允許各 summand endpoint非零；終點項在 finite
   coefficient carrier 中以 linearity 消去，仍不寫 limit endpoint trace。
13. **已完成 C215–C218 test/consumer algebra：**common compact-time bump、四槽 residual jet、
   realizable zero-final algebraic span，以及 complex-transverse/real-reality carriers 均已 kernel-check；
   這些都不是 intrinsic smooth-test topology 或 density theorem。
14. **已完成 C219 density feasibility gate：**projected realizable consumer span 的 closure 落在
   closed residual kernel，unit-initial consumer 證明它不稠密於 whole ambient consumer。此結論
   不排除 residual kernel 內或未來 intrinsic test carrier 內的 density。
15. **歷史 C220–C247 canonical test/tensor quotient與第一個 window-stable slot checkpoint：**whole residual kernel 過大的
   product-moment obstruction、`𝓓(ℝ,ℂ)` zero-final carrier、window/derivative CLMs、separated-test
   bridge、三槽 time/spatial linear consumer、complete algebraic tensor lift、whole-image
   realizability、product/residual closed constraints、fixed/global faithful quotients、all-window
   DirectSum/image、tail vanishing、zero-extension integral及 velocity-slot stability均已 kernel-check。
   contact checkpoint為 `612e758`／`92e2a97`。
16. **歷史 C248–C259 continuation checkpoint：**product-gradient、initial與 complete consumer
   的 cross-window stability，canonical stabilized consumer，分開的 global-time/spatial linearity，
   window-free bilinear map與 global algebraic tensor lift，whole-range realizability、exact image、
   necessary closed constraints、faithful kernel quotient、selected residual factorization及單向
   global image ≤ all-window image均已 kernel-check。contact code/receipt為
   `8e89a6c`／`019842c`；256 modules、3424 source declarations、5254 audited declarations與
   256/256 consistency均通過。
17. **歷史 C260–C271 continuation checkpoint：**C260–C262 將 C259 單向 image inclusion
   經 faithful quotients傳遞並證 residual naturality，但沒有 reverse/equality或新 residual vanishing；
   C263–C271 建立 weighted-`lp 1` transverse coefficient、absolute synthesis、normalized multiplier、
   canonical LF coefficient／continuous-field tests與 separated pure-tensor pointwise bridge。contact
   code/receipt為 `d62ff3085b22448116319f458ab3f929d5c91595`／
   `8a7dfd55fcd7c3fdec587d562695f63238a21dd5`；268 modules、3577 source declarations、
   5586 audited declarations與 268/268 consistency均通過。尚無 coefficient reality、LF completeness、
   intrinsic divergence或 density；C271 witness未證在 composite range。
18. **目前 C272–C283 continuation 已完成並 checkpoint：**coefficient reality、closed
   real-transverse intersection、finite embedding、reality-preserving continuous symbol synthesis、
   diagonal coefficient-symbol cancellation、native-real LF transport與一個 explicit in-range witness
   均已 kernel-check。contact code/receipt為
   `9b08bef28a6849ae53e2381e3ab45001a00f281b`／
   `ff7030b9169114dfa928c8ef5f84d8c14ce9e479`；280 modules、3796 source declarations、
   5943 audited declarations與 280/280 consistency均通過。沒有 intrinsic spatial operator、LF
   completeness、density、weak PDE或 regularity結果；C283也不修補 C271 composite range gap。
19. **建立 intrinsic physical-test carrier：**在已相容封裝的 reality/transverse coefficient carrier
   上，再選擇真正 completed LF tensor／`PiLp 2` physical joint-product carrier，或明確決定弱方程
   全程使用 coordinate quotient classes。新 density/closure目標必須放在 residual kernel內或有
   明確 map的 intrinsic physical-test image內。
20. **補 general weak gradient/coefficient limits 與 test-space weak equation：**逐項通過 time、Stokes、
   Leray/pressure 與 quadratic convection limit；strong carrier convergence本身不自動給這一步。
21. **建立 initial trace 與 limiting energy inequality：**完成後才可 package Leray--Hopf existence；
   再往 local strong、weak--strong uniqueness 與條件正則性推進。Clay 未解核心仍不承諾工期。

## 7. 誠信 gate

以下任一情況出現就不得使用「推進了全域正則性」：

- theorem 只對一個顯式解、steady field、有限 mode 或小資料成立；
- PDE 結論來自 structure field/realization assumption，而非真算子 proof；
- 缺初值、時間區間、div-free、正黏度、函數空間或能量條件；
- `ℝ³` 解空間上不衰減，卻被稱為 finite-energy；
- 把 reachability undecidability、Euler universality 或 Reeb/Beltrami realization 解讀成
  NS blow-up/regularity theorem；
- 把 known conditional criterion 寫成 arbitrary-data global theorem。
- 把 `cutoffStateGradientEnergyT3L2` 稱為完整 `H¹` norm 或 completed Sobolev space；它目前只是
  finite-Fourier homogeneous gradient seminorm squared。
- 從「所有 reconstructed fields 位於共同 `L²` carrier」直接推出 cutoff trajectories coherent、
  convergent 或 compact。
- 把 projected cube initial field 說成未投影 input field；目前只有 projection 與 energy bound。
- 把逐 cube exact field balance 或 spacetime bound 稱為 limiting PDE energy inequality、
  Leray--Hopf weak solution 或三維 existence/smoothness 結果。
- 把 `Classical.choice` 得到的 cutoff-indexed family 稱為 canonical、computable、cross-cutoff
  coherent 或 measurable-in-parameters 的 family。
- 把 C182 的逐 cutoff time continuity 稱為 cutoff-uniform equicontinuity、time-derivative bound
  或 compactness。
- 把 C186 的 projected-convection squared `H⁻³` energy bound 稱為 full Galerkin RHS bound、
  trajectory time-derivative estimate、intrinsic torus Sobolev theorem 或 compactness。
- 把 C187 這塊 static theorem 本身稱為 trajectory theorem；actual transport 與 time integration
  分別來自 C188、C189。
- 把 C191 這塊 squared theorem 本身稱為 equicontinuity theorem；standard equicontinuity package
  是 C192 的下游結果。
- 把 C192 在 coefficient `H⁻³` carrier 的 `UniformEquicontinuousOn` 稱為 field-`L²`
  equicontinuity、spatial compactness、Arzelà--Ascoli、subsequence、weak PDE solution 或三維
  regularity。
- 把 C193 的 integrated high-tail bound 稱為逐時、`sup_t` 或 `C_tL²_x` tail control。
- 把 C194 對每個 fixed `M` 的 low-mode field equicontinuity 稱為 uniform-in-`M` 或 full-field
  equicontinuity；recovery operator norm 明確依賴 `M`。
- 把 C195 的 static pointwise energy/dissipation sublevel compact closure 直接套到 C181 actual
  trajectory family；後者目前只有 time-integrated dissipation bound。
- 把 C197 的 fixed-low-mode compact closure 稱為 full-field compactness。
- 把 `CurrentT3CompactIntervalL2` 冒充 canonical `L²([a,b]×T³;ℂ³)`；它是 iterated
  `Lp_t (Fin 3 → Lp_x)`，內層 Pi norm 是三分量 scalar norms 的 supremum。
- 把 C198 本身稱為 whole-forward-ray compactness；其 limit 與 `StrictMono` subsequence 可依賴
  fixed interval，`a=b` 時 carrier 甚至退化為零測度 quotient。
- 把 C198 的 abstract quotient-`Lp` limit 直接當成具代表元、real、div-free、attains initial
  data 的 velocity field，或由其 strong carrier convergence直接推出 quadratic convergence、
  weak Navier--Stokes equation、energy inequality 或 Leray--Hopf solution。
- 把 C199 的 dependent product convergence 稱為 single global forward-ray `L²` convergence；
  product coordinates 是不同 finite-window quotient carriers。
- 把 C200 的 compatible local quotient classes 直接 glue 成 global measurable representative，
  或把 restriction compatibility 稱為 initial trace、constraint preservation、energy inequality、
  weak PDE identification 或 Leray--Hopf existence。
- 把 C201 的 projective-limit-style subtype 稱為 single global-norm `L²_loc` function space、
  chosen representative，或由 subtype convergence 直接推出 pointwise/PDE convergence。
- 把 C202 的 squared-norm `1,3` comparison（等價的 norm constants 是 `1,√3`）稱為等距、canonical joint-product
  `L²([a,b]×T³;ℂ³)` identification、Fubini equivalence 或 global representative。
- 把 C203 的 coordinate map 稱為 surjective、onto whole product 的 equivalence、isometry或
  image characterization；ambient exhaustion product 允許不相容的跨視窗系統，compatibility
  只保證在 embedded image 中。
- 從 C203 本身的 coordinate convergence 直接推出 velocity products、joint-product `L¹`
  convergence、representative-level convergence 或 nonlinear weak-PDE passage；C203 本身未定義
  multiplication，這個缺口由 C204 關掉，但不能因此跳到 weak PDE。
- 把 C204 的 iterated `L¹_t(L¹_x)` target 稱為 joint-product/Fubini `L¹`，或把 separate
  a.e.-in-space／a.e.-in-time formulas flatten 成 joint-product a.e. representative。
- 把 C204 本身的 unrestricted `(m,i,j)` product convergence 稱為 cross-window compatible；該步
  由 C205 另證。但 C205 仍不給 single global norm、global representative 或 joint/Fubini class。
- 把 C205 的 outer-time compatibility flatten 成 joint-product/Fubini a.e. equality，或把 ambient
  compatible submodule 說成 quadratic image characterization。它也尚未給 intrinsic tensor、
  divergence、convection、pressure 或 weak PDE term。
- 把 C206 的 literal nested integral 稱為 joint/Fubini integral，或把
  `Icc a b →ᵇ (T3 →ᵇ ℂ)` 說成全部 product-continuous／smooth／compactly-supported tests。C206
  沒有 derivative、density、test restriction/extension、integration by parts 或 weak equation。
- 把 C206 fixed-test scalar convergence 稱為 uniform-over-tests、distributional PDE convergence、
  新 compactness 或新的 global `L¹` strong topology；它只是 C205 compatible-carrier convergence
  經固定 window-coordinate CLM 的 continuous image，且 pairing 是無 conjugation的 complex bilinear。
- 把 C207 的 unsigned `ΣᵢΣⱼ∫ₜ∫ₓ η∂ⱼϕᵢ Pᵢⱼ` 稱為 signed convection term、Galerkin weak
  identity 或 limiting Navier--Stokes equation。C207 本身沒有 cross-duality；C208 雖已另證
  Hermitian cross-Parseval／cross-gradient／Stokes，但仍沒有把它接到 C207 bilinear convention。
  C209 雖只給 triple selection與兩側 zero-sum expansions，C210 已補 signed
  transversality/reindexing、reflected Leray removal與 static RHS；C211 已補 scalar time envelope、
  endpoint/FTC與 fixed-cutoff separated spacetime identity。cutoff-limit passage、一般 test-space
  integration by parts與 initial trace仍缺。
- 把 C207 finite-Fourier derivative tests 說成一般 smooth、compactly supported、dense、real 或
  divergence-free test space；也不可把 exact cover derivative 冒充 arbitrary quotient-torus
  intrinsic differential calculus。
- 把 C207 fixed finite-Fourier functional convergence 稱為 uniform-over-tests、distributional PDE
  convergence或新 compactness；它只是 C205 compatible-carrier convergence 經一個固定 finite-sum
  CLM 的 continuous image，且尚未另證 specialized functional 非零。
- 把 C208 Hermitian cross-Parseval／cross-gradient／Stokes duality直接等同 C207 的 bilinear
  product-gradient functional。arbitrary complex tests 下兩者可不同；尚需 conjugate symmetry、
  frequency reflection與適當 convention bridge。C209 的 bilinear zero-sum expansions沒有自動
  證這個 Hermitian identification。
- 把 C208 的 cross-gradient稱為 signed convection、Leray-projected static RHS、Galerkin weak
  identity或 limiting PDE；它 differentiates both test and state fields，沒有 quadratic velocity
  product、time envelope、endpoint/FTC或 subsequence passage。
- 把 C209 的 physical product-gradient component expansion與 reflected coefficient convection
  expansion稱為已彼此相等。C209 只證兩邊各自帶同一 `p+q+r=0` constraint；`p↔q` reindex、
  transversality與 global minus sign尚未組成 theorem。
- 把 C209 的 reflected coefficient expansion稱為 Leray removal、pressure cancellation、signed
  static Galerkin RHS、fixed-cutoff weak identity或 limiting weak PDE；它沒有這些運算或 time term。
- 把 C210 的 static reflected RHS稱為 fixed-cutoff spacetime weak identity或 limiting PDE。C210
  沒有 time envelope、product rule、endpoint/FTC、subsequence passage或 initial trace；它也沒有
  把 complex-bilinear pairing等同 C208 Hermitian convention。`-r` reflection不可刪除。
- 把 C211 的 fixed-cutoff separated spacetime identity稱為 limiting weak PDE、arbitrary smooth-test
  formulation、initial trace或 Leray--Hopf theorem。C211 尚未沿 C205 的同一 subsequence取極限；
  `eta(t)d(x)`、finite cutoff、complex-bilinear pairing與 `-r` reflection 都是正式範圍的一部分。
- 把九個 complex ordered products `u_i u_j` 直接稱為 intrinsic tensor、divergence、convection、
  pressure 或 weak nonlinear PDE term；也不可把 quadratic diagonal operation 稱為 continuous
  linear map、injective map 或 embedding。
- 在沒有 `ν>0` 時宣稱 C204／C205／C207 的 actual Galerkin same-`U,φ` wrappers，或宣稱已從
  actual family 取得 C206／C207 所消費的 `hP`。抽象 Hölder、generic restriction／pairing 與 conditional
  arbitrary-filter product／subtype／pairing theorems本身是 viscosity-free。
- 把 C196–C211 統稱為 Aubin--Lions；C196–C202 的 compactness proof 是 finite-mode
  Arzelà--Ascoli 加 quantitative Fourier-tail，C203 是下游 coordinate topological embedding，
  C204 是再下游 Hölder product convergence，C205 是更下游 restriction/carrier packaging，C206
  是 fixed-test continuous image，C207 是 finite-sum fixed-functional specialization，C208 是
  static finite-Fourier Hermitian duality，C209 是更下游 finite algebra expansion，C210 是再下游
  static signed assembly，C211 是 fixed-cutoff product-rule／FTC assembly；均沒有套用
  Aubin--Lions theorem。

這份 roadmap 的成功標準，是把已知分析逐層 machine-check，並把最後未知的一步準確孤立；
不是用形式化包裝掩蓋數學仍未知。
