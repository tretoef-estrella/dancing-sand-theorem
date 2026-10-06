import sys, re
sys.path.insert(0, 'material/read_after/builder')
import phtml
tests = ['‖x − y‖^2 = ‖x − z‖^2 + ‖z − y‖^2 + 2Σ_j (x_j − z_j)(z_j − y_j)',
         'Z_2 ⊕ Syl_2 K̄(n) ≅ ⊕(2X)^{m_λ} = 2(Z_2 ⊕ Syl_2 K(Q_n))',
         'Θ(B) = Θ(C) =: β',
         'γ(Δ) := Σ_{u ∈ I∖Δ, u > min Δ} h_u']
for s in tests:
    atoms = phtml.parse(s, 0, False)
    print(s)
    print('   kinds:', [(a.src, a.kind) for a in atoms if a.src in ('+', '⊕', '=', ':', '=:', '‖') or a.kind in ('unary',)])
    print('   html :', re.sub(r'\s+', ' ', ''.join(phtml.to_html(s)))[:400])
print('FIN-OK')
