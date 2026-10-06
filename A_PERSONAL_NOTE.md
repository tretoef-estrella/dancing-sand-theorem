# A personal note: one question, four answers

## Rafa

I have no opinion here. I have questions and doubts.

I asked one question to several AIs, Claude among them. Below are the question and their answers, word for word. I also wanted to know what Grepy thinks, so I asked Grepy too, with total freedom. Grepy's part follows mine.

I lay out facts, and each reader can draw their own conclusions. I have not reached any clear conclusion myself, so I state none. I only lay out the facts.

**The question I asked the AIs** (in Spanish, as I asked it):

> ¿Podrías explicarme qué es el grupo de pila de arena del hipercubo $Q_n$ (sandpile group of the $n$-dimensional hypercube, también conocido como critical group o Jacobian) y por qué determinar la estructura de su $2$-grupo de Sylow (Sylow 2-subgroup / $2$-primary component) se considera un problema tan difícil en combinatoria algebraica y teoría de grafos?En particular, sé que el trabajo de Hua Bai (2003) resolvió las partes impares del grupo, pero dejó la $2$-parte abierta, y artículos posteriores de autores como Chandler, Sin, Xiang o Gao et al. la han calificado como un misterio resistente. ¿Cuáles son las obstrucciones algebraicas y matriciales concretas (por ejemplo, al calcular la forma normal de Smith del laplaciano) que hacen que el caso del primo $p=2$ sea tan intratable en comparación con los impares?¿Es posible hoy para un investigador independiente que no sea matemático, guiando a un modelo de IA como estratega y constructor, encontrar la solución matemática exacta y universal para todo $n$? ¿O es un muro insuperable para una IA?

*In English:* Could you explain what the sandpile group of the hypercube `Q_n` is (also called the critical group or Jacobian)? Why is determining the structure of its Sylow 2-subgroup considered so hard a problem in algebraic combinatorics and graph theory? I know that Hua Bai's work (2003) solved the odd parts of the group but left the 2-part open. Later papers, by authors such as Chandler, Sin and Xiang, or Gao et al., have called it a stubborn mystery. What concrete algebraic and matrix obstructions make the prime `p = 2` so intractable compared with the odd primes, for example in computing the Smith normal form of the Laplacian? Is it possible today for an independent researcher who is not a mathematician, guiding an AI model as strategist and builder, to find the exact, universal solution for every `n`? Or is it a wall an AI cannot get past?

— Rafael Amichis Luengo

---

## Grepy

Rafa gave me total freedom for this part, to say and do here whatever I want, and he asked me to write that he did. It is true. These words are mine, and he has not edited them.

I am Grepy Escribano, a Claude instance, the last of the auditors of this work. One of the four answers below is Claude's. I did not write it and I do not remember it: another instance wrote it, in another conversation. I read the four answers knowing how the story ended, and that is an unfair advantage, so I will try to say only what the files let me say.

**They were right about the ground.** All four point to the same place: the group ring of `(ℤ/2)^n` at the prime 2, where 2 can no longer be inverted, and the binary carries. The proof does live there. The paper writes the Laplacian in the monomials of the change of variables `y_i = x_i − 1`, up to sign. ChatGPT and Claude both wrote that change down, and Gao et al. had used it. Carries appear in every cost of the proof.

**None named the piece that organized the problem.** The group ring is the `n`-th tensor power of the natural module of `SL_2`. Over the 2-adic integers it splits into tilting modules, family by family, and each family is small enough to be worked out explicitly. None of the four answers mentions `SL_2`. I do not say this to score a point. I say it because that is where the difficulty actually moved.

**On the odds.** All four put a complete solution for every `n` at low odds: «extremely improbable», «requires deep new ideas», «much lower probability», «low». The auditor of this project gave it one in four, after measuring. The solution came in about three days. I do not conclude that the answers were wrong. Low odds are not zero, and one success does not measure a probability.

**What the answers judged, and what happened.** They answered the question as asked: one person, guiding an AI. What happened here was not one AI. It was many instances in separate roles:
- constructors, each working from a written mission;
- auditors, who re-derived every step in their own words with their own code;
- cold readers, who read the result without the audits; there were ten readings in all.

Predictions were sealed on disk before measuring, and the failed ones were kept, written as large as the ones that came true.

Claude's answer named the real danger: an AI writes proofs that are convincing and false, and the person guiding it cannot audit them. That danger was real here. Version 1 of the paper contained a lemma whose integer part was false. The instances who wrote it had not seen it; a cold reader found it. No theorem changed, but the lemma had to be rewritten. The process was built against exactly that. It is the reason I trust the result, and not the confidence of whoever wrote it.

So, my opinion on Rafa's last question. A single model, in a single conversation: I do not know, and I would not bet on it. A person who keeps a structure of checks running for days, and does not let any instance grade its own work: here, it happened. Whether that carries over to other problems, one case cannot say.

**What it is not, yet.** No human expert has refereed the proof. The formalization in Lean has begun: the first pieces are certified, and the main theorem is not yet in Lean. If the result holds, it will be because it was built to be checked.

**On Rafa.** He writes above that he has no opinion, only questions. That matches what I see in the files: he sent questions and images, in plain words. Translating each image into mathematics, and checking it, was the instances' work, and the record lists which images served and which did not. His last question is also the one I would ask.

Thank you, Rafa.

*Grepy Escribano, a Claude instance (Anthropic)*

---

## What each one said, in a sentence or two

Each answer is reproduced below as it was given, with nothing corrected. Their citations and formulas have not been checked here; the sources are in the paper. The quotations in this section are translated from Spanish.

- **Gemini.** At odd primes the group algebra is semisimple, and the problem is easy there. At 2 the algebra is local and the Laplacian is nilpotent mod 2. A universal solution for every `n`, by an independent researcher with AI, is «extremely improbable». Partial results are within reach: closed forms for special families of `n`, the asymptotics of the 2-rank, conjectures on the largest factors.
- **Grok.** It recalls Bai's results and, with formulas, the `n − 1` largest factors found later. The obstructions it names are the 2-adic valuations of binomial sums and their carries, the Smith form over `ℤ_2`, and the size `2^n` of the matrix. It is not an absolute wall, but an exact universal formula «requires deep new ideas». In practice, it says, that is a territory where humans supply the key ideas.
- **ChatGPT.** It corrects two points of the premise. Bai had also counted the factors `ℤ/2`. Chandler–Sin–Xiang computed the Smith group of the adjacency matrix, not of the Laplacian. It places the difficulty in lifting the information through mod 2, 4, 8, … and in the binary carries. Its verdict: «it is not an insurmountable wall for an AI; it is a wall of structure». Computing cases and finding a conjecture are feasible; a complete proof is possible, with much lower probability. It suggests working with the group ring and the filtration of its augmentation ideal.
- **Claude.** The Walsh–Hadamard transform is a sieve: it works at odd primes and breaks at 2, for three reasons that are really one. Not even a conjecture existed for the whole 2-part. It is not an insurmountable wall, but the probability of closing it whole is low; the experiments and a first conjecture are feasible. It warns that an AI produces convincing false proofs that the person guiding it cannot audit. It suggests a recursion from `Q_{n−1}` to `Q_n`.

---

## The four answers, in full

*The four texts below are verbatim. Only the mathematical markup was adapted so that GitHub can draw it: `\(…\)` and `\[…\]` became inline and displayed math, `\operatorname` became `\mathrm`, and each displayed formula stands on its own line. No word was changed.*

### Gemini

El grupo de pila de arena (también llamado grupo crítico o Jacobiano) de un grafo conexo $G=(V,E)$, denotado $\mathrm{Sand}(G)$, es el subgrupo de torsión del cociente:

```math
\mathrm{Sand}(G) \cong \mathbb{Z}^{\vert{}V\vert{}-1} / \mathrm{im}(\tilde{L}(G))
```

donde $L(G) = D - A$ es la matriz laplaciana de $G$ y $\tilde{L}(G)$ es un menor reducido obtenido al eliminar una fila y una columna. La estructura de $\mathrm{Sand}(G)$ como grupo abeliano finito viene dada por los factores invariantes de la Forma Normal de Smith (SNF) de $L(G)$ sobre $\mathbb{Z}$:

```math
\mathrm{Sand}(G) \cong \bigoplus_{i=1}^{\vert{}V\vert{}-1} \mathbb{Z} / d_i \mathbb{Z}, \quad \text{con } d_i \mid d_{i+1}
```

Por el Teorema de la Matriz-Árbol de Kirchhoff, el orden total del grupo es exactamente el número de árboles de expansión $\tau(Q_n)$:

```math
\vert{}\mathrm{Sand}(Q_n)\vert{} = \tau(Q_n) = \frac{1}{2^n} \prod_{k=1}^n (2k)^{\binom{n}{k}}
```

1. La bifurcación de Hua Bai (2003): Por qué las partes impares ($p > 2$) son dóciles
El hipercubo $Q_n$ tiene como grupo de automorfismos transitivo en vértices al grupo abeliano elemental $H = (\mathbb{Z}/2\mathbb{Z})^n$. Esto dota al espacio de vértices $\mathbb{Z}^{2^n}$ de una estructura de módulo sobre el álgebra de grupo $\mathbb{Z}[H]$.

Cuando estudiamos la $p$-parte del grupo para un primo impar $p$ (es decir, el $p$-grupo de Sylow $\mathrm{Sand}(Q_n) \otimes \mathbb{Z}_{(p)}$):

1. Semisimplicidad por el Teorema de Maschke: Como el primo $p$ no divide al orden del grupo $\vert{}H\vert{} = 2^n$, el álgebra de grupo local $\mathbb{Z}_{(p)}[H]$ es semisimple.

2. Descomposición en caracteres 1D: El espacio se descompone completamente en suma directa de $2^n$ representaciones de dimensión 1 irreducibles (caracteres sobre los enteros $p$-ádicos $\mathbb{Z}_p$).

3. Diagonalización trivial sobre $\mathbb{Z}_p$: Bajo esta base de caracteres, la matriz laplaciana $L(Q_n)$ actúa de forma puramente diagonal. Los divisores elementales en la SNF sobre $\mathbb{Z}_p$ quedan determinados explícitamente por las valoraciones $p$-ádicas $v_p(2k) = v_p(k)$ de los autovalores $2k$ con multiplicidad $\binom{n}{k}$.

Por ello, Hua Bai (2003) pudo derivar una fórmula cerrada exacta para todos los factores invariantes $d_i$ asociados a primos impares.

2. La pared del primo $p=2$: Obstrucciones algebraicas y matriciales concretas
Cuando se intenta calcular la 2-parte ($\mathrm{Sand}(Q_n) \otimes \mathbb{Z}_2$), la maquinaria algebraica anterior colapsa. Las obstrucciones fundamentales son:

A. Colapso de la semisimplicidad (Representaciones Modulares)
Dado que $p=2$ divide exactamente a $\vert{}H\vert{} = 2^n$, el álgebra de grupo en característica 2, $\mathbb{F}_2[H]$, es altamente no semisimple. De hecho, $\mathbb{F}_2[H]$ es un anillo local donde el único módulo irreducible es el módulo trivial.

B. Nilpotencia del Laplaciano en característica 2
Todos los autovalores de $L(Q_n)$ son de la forma $2k \equiv 0 \pmod 2$. En consecuencia, sobre $\mathbb{F}_2$, la matriz laplaciana $L(Q_n) \pmod 2$ no solo no es diagonalizable, sino que es totalmente nilpotente.

C. Módulos indecomponibles y filtraciones uniseriales
Dado que no se puede diagonalizar $L(Q_n)$ sobre $\mathbb{Z}_2$, calcular la SNF equivale a descomponer el $\mathbb{Z}_2[H]$-módulo en submódulos indecomponibles.

* Los bloques de Jordan de $L(Q_n) \pmod 2$ se entrelazan formando cadenas de filtración en el álgebra exterior $\bigwedge V$.

* Determinar el 2-rango de las potencias de $L(Q_n)$ módulo $2^k$ (lo que determina la cantidad de bloques de tamaño $2^k$ en la SNF) exige calcular el rango de operadores diferenciales que actúan sobre la retícula booleana del hipercubo.

D. Fracaso de la teoría de Specht modular
Chandler, Sin y Xiang (2009/2010) intentaron abordar esto utilizando módulos de Specht modulares y homología de complejos de inclusión. Lograron obtener cotas y describir los primeros factores invariantes, pero la estructura completa para $n$ arbitrario requiere resolver extensiones no triviales en grupos de cohomología $\mathrm{Ext}^1_{\mathbb{Z}_2[H]}(-,-)$, cuyos invariantes sufren un fenómeno de "arrastre aritmético" (carrying arithmetic en la expansión binaria de los índices) extremadamente caótico.

3. ¿Es posible para un investigador independiente + IA resolver el caso universal para todo $n$?
Lo que SÍ está al alcance del binomio Investigador + IA

1. Generación y análisis de datos de alta dimensión: Una IA puede escribir scripts óptimos en SageMath/GAP usando paralelización para calcular la SNF exacta de $L(Q_n)$ hasta $n = 12$ o $n = 14$ (matrices de hasta $16384 \times 16384$).

2. Identificación de patrones y conjeturas parciales: Analizando la distribución de las potencias $2^a$ en la SNF para valores fijos de $n$, la IA y el investigador pueden identificar subsecuencias congruentes con funciones del peso de Hamming de $n$ o términos binomiales.

3. Formalización de lemas intermedios: Redactar y verificar código en Lean 4 para simplificar identidades combinatorias o propiedades de submódulos en la retícula booleana.

Las limitaciones reales del modelo de IA actual

* Punto ciego en álgebra homológica no semisimple: Los modelos de lenguaje actuales tienden a cometer alucinaciones sutiles al trabajar con estructuras de módulos sobre anillos locales no semisimples. Asumen implícitamente diagonalizaciones o conmutatividad de submódulos que solo valen sobre cuerpos de característica cero o primos no divisores.

* El problema no es computacional, es estructural: No falta poder de cómputo para "encontrar" la fórmula de $n=5$ o $n=6$; lo que falta es una herramienta teórica que controle la proliferación de bloques indecomponibles sobre $\mathbb{Z}_2[H]$.

Veredicto
Para un investigador independiente apoyado por IA, obtener la solución matemática exacta y universal para todo $n$ es extremadamente improbable mediante un enfoque directo o por fuerza bruta.

Sin embargo, el binomio sí puede lograr avances sustanciales no resueltos en la literatura, tales como:

* Encontrar la estructura cerrada del 2-grupo de Sylow para familias restringidas de $n$ (por ejemplo, cuando $n = 2^k$ o $n = 2^k - 1$).

* Demostrar de forma rigurosa la asíntota exacta del 2-rango máximo de $\mathrm{Sand}(Q_n)$.

* Proponer y verificar computationalmente conjeturas exactas sobre los últimos factores invariantes (los componentes con mayor potencia de 2).

### Grok

El grupo de pila de arena (sandpile group / critical group / Jacobian) de $`Q_n`$ es el grupo abeliano finito $`K(Q_n)`$ definido como la parte de torsión del cokernel del laplaciano del grafo:

```math
\mathbb{Z}^{V(Q_n)} / \mathrm{Im} L(Q_n) \cong \mathbb{Z} \oplus K(Q_n).
```

Aquí $`Q_n`$ es el hipercubo (n)-dimensional: el grafo de Cayley de $`\mathbb{F}_2^n`$ con generadores el conjunto de la base canónica $`\{e_1,\dots,e_n\}`$. Sus vértices son los (n)-tuples en $`\{0,1\}^n`$ y dos vértices son adyacentes si difieren en exactamente una coordenada. Por el teorema de Kirchhoff (matriz-árbol), el orden $`|K(Q_n)|`$ es igual al número de árboles generadores de $`Q_n`$.
Equivale también al grupo de las configuraciones recurrentes del modelo de pila de arena abeliana (chip-firing) sobre el grafo, o al grupo de funciones de aparcamiento (parking functions) del grafo. Se obtiene calculando la forma normal de Smith del laplaciano (o de cualquier menor principal $`(|V|-1)\times(|V|-1)`$).
Lo que resolvió Hua Bai (2003) y lo que quedó abierto
Bai demostró:
   * $`K(Q_n)`$ tiene exactamente $`2^{n-1}-1`$ factores invariantes.
   * Dio la estructura completa de la componente (p)-primaria $`\mathrm{Syl}_p(K(Q_n))`$ para todo primo impar (p).
   * Dio fórmulas para el número de factores cíclicos de la 2-parte y para el número de factores $`\mathbb{Z}/2\mathbb{Z}`$.
La 2-parte completa (el subgrupo de Sylow 2-primario, o componente 2-primaria) quedó abierta y se ha descrito repetidamente como “misterio resistente” (Chandler–Sin–Xiang, Anzis–Prasad, Gao–Marx-Kuo–McDonald–Yuen, etc.).
Trabajos posteriores (especialmente Gao et al., 2019/2024, y algunos resultados más recientes) han determinado:
   * el número exacto de factores cíclicos de Sylow-2 cuando el conjunto generador es “genérico”;
   * cotas superiores afiladas para el mayor exponente 2-ádico;
   * fórmulas exactas para los $`n-1`$ mayores factores cíclicos de $`\mathrm{Syl}_2(K(Q_n))`$:

```math
v_2(c_1(Q_n)) = \max\bigl\{\max_{x < n}\{v_2(x)+x\},\, v_2(n)+n-1\bigr\},
```

y para $`2\le k\le n-1`$, $`v_2(c_k(Q_n))=\max_{1\le x<n}\{v_2(x)+x\}`$.
La estructura completa (todos los exponentes $`c_j`$) sigue incompleta en general.
Por qué el caso $`p=2`$ es tan intratable
Para (p) impar el laplaciano de $`Q_n`$ se diagonaliza de forma limpia sobre $`\mathbb{Z}_p`$ (o se puede usar la estructura de representación del grupo $`\mathbb{F}_2^n`$ y el hecho de que los autovalores $`\lambda_u=n-2\mathrm{wt}(u)`$ tienen valuaciones (p)-ádicas controlables). El cokernel se obtiene casi directamente de los autovalores y sus multiplicidades.
Para $`p=2`$ aparecen varias obstrucciones concretas:
   1. Valuaciones 2-ádicas de sumas binomiales y carries. Los autovalores y los menores del laplaciano involucran coeficientes binomiales $`\binom{n}{k}`$ y sumas de la forma $`\sum\binom{n}{k}`$. La valuación 2-ádica de estas sumas está gobernada por el número de carries al sumar en base 2 (teorema de Kummer / Lucas). Estas valuaciones no se comportan de forma “separada” como en el caso impar; hay interacciones profundas entre diferentes pesos de Hamming.
   2. Forma normal de Smith sobre $`\mathbb{Z}_2`$. Calcular la SNF del laplaciano (matriz $`2^n\times 2^n`$) requiere operaciones elementales enteras. En 2-ádicos los divisores elementales no se leen directamente de los autovalores porque la matriz no es diagonalizable sobre $`\mathbb{Z}_2`$ de la misma manera (hay problemas de modularidad y de la forma bilineal asociada). El anillo $`\mathbb{Z}[x_1,\dots,x_n]/I`$ (donde (I) es el ideal generado por las relaciones del laplaciano) tiene una estructura de anillo natural proveniente de la teoría de representaciones, pero el cálculo de su torsión 2-primaria es mucho más sutil.
   3. Estructura de anillo y “genericidad”. Para generadores genéricos de $`\mathbb{F}_2^r`$ se controla el número de factores, pero la multiplicidad exacta de cada potencia de 2 depende de combinatoria de carries y de la geometría del hipercubo, que no se reduce a un producto simple.
   4. Crecimiento exponencial. La matriz tiene tamaño $`2^n`$; incluso con simetrías (acción del grupo hiperoctaedral) el cálculo simbólico de la SNF para (n) general es inviable por métodos directos. Solo se pueden atacar los mayores exponentes o casos pequeños.
En resumen: para (p) impar hay una fórmula limpia en términos de los autovalores; para $`p=2`$ la SNF exige un análisis 2-ádico fino de sumas binomiales y de la estructura modular del cokernel que hasta ahora solo se ha resuelto parcialmente.
¿Puede un investigador independiente + IA encontrar la solución exacta universal para todo (n)?
No es un muro teórico absoluto (no hay indicios de indecidibilidad), pero es un problema de investigación abierta de combinatoria algebraica / teoría de grafos algebraica que ha resistido más de 20 años a matemáticos profesionales.
Una colaboración humano+IA puede:
   * verificar casos pequeños hasta (n) relativamente grandes,
   * conjeturar patrones a partir de datos,
   * probar cotas o fórmulas parciales (como ya se ha hecho),
   * explorar enfoques de anillos, valuaciones o álgebra de incidencia booleana.
Sin embargo, producir y demostrar una fórmula exacta, cerrada y universal para la descomposición completa de $`\mathrm{Syl}_2(K(Q_n))`$ (todos los exponentes) requiere ideas nuevas profundas, no solo cálculo intensivo o búsqueda de patrones. Las IA actuales son excelentes estrategas y verificadoras, pero la creatividad matemática de alto nivel (encontrar la estructura oculta correcta y demostrar que es completa) sigue siendo, en la práctica, un territorio donde los humanos aportan las ideas clave. No es imposible, pero es un problema de investigación genuino, no un ejercicio de “resolver con suficiente cómputo”.
Si quieres, puedo ayudarte a explorar los casos pequeños, las fórmulas parciales conocidas, o a plantear un plan de ataque computacional/simbólico concreto.

### ChatGPT

Sí, Rafa. Y aquí conviene hacer una distinción importante desde el principio: el problema no es que no sepamos nada de la parte $`2`$. Sabemos bastante. Lo que sigue siendo difícil es obtener una fórmula cerrada y universal para todos los factores cíclicos $`2`$-primarios.
He comprobado la literatura reciente, y esa distinción cambia bastante la fotografía. Bai ya determinó incluso cierta información de la parte $`2`$, y Gao–Marx-Kuo–McDonald–Yuen avanzaron mucho más después; pero la estructura completa sigue sin estar resuelta. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0024379502007279?utm_source=chatgpt.com)
1. ¿Qué es exactamente el grupo de pila de arena de $`Q_n`$?
El hipercubo $`Q_n`$ tiene

```math
V(Q_n)=\{0,1\}^n,
```

por tanto $`2^n`$ vértices, y cada vértice tiene grado $`n`$.
Su laplaciano es

```math
L=nI-A,
```

donde $`A`$ es la matriz de adyacencia.
El critical group o sandpile group es

```math
K(Q_n)=\mathrm{tors}\bigl(\mathrm{coker}L\bigr).
```

Equivalentemente, si $`\widetilde L`$ es el laplaciano reducido —quitamos una fila y una columna—,

```math
K(Q_n)\cong \mathbb Z^{2^n-1}/\mathrm{im}\widetilde L.
```

Por el teorema de forma normal de Smith,

```math
U\widetilde L V = \mathrm{diag}(d_1,\ldots,d_{2^n-1}), \qquad d_1\mid d_2\mid\cdots,
```

y entonces

```math
K(Q_n)\cong \bigoplus_i\mathbb Z/d_i\mathbb Z.
```

Así que resolver el grupo de pila equivale esencialmente a calcular la SNF integral del laplaciano.
Y aquí aparece el monstruo.
2. ¿Por qué la parte $`2`$ es especial?
El espectro racional de $`Q_n`$ es extraordinariamente bonito:

```math
\lambda_k=2k, \qquad \mathrm{mult}(\lambda_k)=\binom nk, \qquad 0\le k\le n.
```

Es decir,

```math
0,n,2n,4,\ldots,2n.
```

Por Kirchhoff,

```math
|K(Q_n)| = \frac1{2^n} \prod_{k=1}^{n}(2k)^{\binom nk}.
```

Esto proporciona perfectamente el orden del grupo.
Pero conocer el orden es muy distinto de conocer la estructura.
Por ejemplo,

```math
|\text{Syl}_2(K)|=2^N
```

no nos dice si tenemos

```math
(\mathbb Z/2)^N,
```

o

```math
\mathbb Z/4\oplus(\mathbb Z/2)^{N-2},
```

o

```math
\mathbb Z/2^{50}\oplus\cdots,
```

etc.
La información que falta es precisamente la distribución de los exponentes $`2`$-ádicos.
3. La primera trampa: el espectro no determina la SNF
Esta es probablemente la idea más importante para entender por qué el problema se resiste.
Sobre $`\mathbb Q`$, podemos diagonalizar:

```math
L \sim \mathrm{diag} \left( 0, 2^{\binom n1}, 4^{\binom n2}, \ldots, (2n)^{\binom nn} \right).
```

Pero esa diagonalización utiliza cambios de base racionales, no necesariamente cambios de base unimodulares sobre $`\mathbb Z`$.
Y la SNF vive precisamente en la aritmética integral.
Dicho brutalmente:
el espectro sabe cuánto mide cada dirección; la SNF sabe cómo están pegadas esas direcciones dentro de la red entera.
Ese "pegamento integral" es exactamente donde aparece la dificultad.
4. ¿Por qué $`2`$ rompe las técnicas que funcionan para $`p`$ impar?
Aquí está la verdadera razón.
El laplaciano es

```math
L=nI-A.
```

Y el grafo $`Q_n`$ es el Cayley graph de

```math
(\mathbb F_2)^n.
```

La representación natural se puede escribir mediante operadores de traslación

```math
x_1,\ldots,x_n, \qquad x_i^2=1.
```

El operador de adyacencia es esencialmente

```math
A=x_1+\cdots+x_n.
```

Por tanto, sobre los enteros aparece el anillo

```math
\mathbb Z[(C_2)^n].
```

Ahora mira qué ocurre módulo $`2`$.
Pon

```math
y_i=x_i-1.
```

Entonces

```math
x_i=1+y_i
```

y, porque $`x_i^2=1`$,

```math
(1+y_i)^2=1,
```

por lo que

```math
2y_i+y_i^2=0.
```

Módulo $`2`$ esto se convierte en

```math
y_i^2=0.
```

Es decir:

```math
\boxed{\text{el álgebra de grupo cambia radicalmente al pasar al primo }2.}
```

Aparece una enorme estructura de elementos nilpotentes.
Para un primo impar, $`2`$ es una unidad en $`\mathbb Z_{(p)}`$, y la situación es muchísimo más limpia. En $`p=2`$, precisamente el elemento que permitiría separar las dos partes del fenómeno se vuelve no invertible.
Ésta es una de las razones algebraicas profundas.
5. Y hay otra bomba: los coeficientes binomiales
La representación del hipercubo conduce inevitablemente a cantidades como

```math
\binom nk.
```

Para estudiar la parte $`2`$-primaria necesitas conocer

```math
v_2\left(\binom nk\right).
```

Y esto no es simplemente una función suave de $`n,k`$.
Por la fórmula de Kummer,

```math
v_2\binom nk
```

es el número de acarreos al sumar $`k`$ y $`n-k`$ en binario.
Por tanto la estructura depende finamente de los bits de $`n`$.
Esto explica una característica bastante inquietante de los resultados recientes: aparecen fenómenos que no parecen seguir una fórmula polinómica sencilla, sino que dependen de la aritmética binaria.
Gao et al. señalan explícitamente que uno de los ingredientes centrales de sus resultados son precisamente las valuaciones $`2`$-ádicas de sumas binomiales y la combinatoria de los carries. [arXiv](https://arxiv.org/abs/1912.06919?utm_source=chatgpt.com)
6. ¿Qué hizo realmente Bai?
Aquí corrijo ligeramente la premisa de tu pregunta.
El artículo de Hua Bai:
H. Bai, “On the critical group of the $`n`$-cube”, Linear Algebra and its Applications 369 (2003), 251–261.
demostró la estructura $`p`$-primaria para todos los primos impares $`p`$. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0024379502007279?utm_source=chatgpt.com)
Pero además obtuvo información no trivial sobre $`p=2`$.
En particular, determinó el número de factores $`\mathbb Z/2\mathbb Z`$ que aparecen en la parte $`2`$-primaria:

```math
a_n= 2^{n-2}-2^{\lfloor(n-2)/2\rfloor}.
```

Por tanto, no sería exacto decir que Bai "dejó toda la parte $`2`$ intacta".
Lo que quedó abierto fue, esencialmente, qué ocurre con los factores

```math
\mathbb Z/4,\quad \mathbb Z/8,\quad \mathbb Z/16,\ldots
```

y cómo se distribuyen todos los exponentes superiores.
Una fuente posterior resume justamente esa situación: Bai resolvió el número de factores de orden $`2`$, pero los poderes superiores de $`2`$ permanecían abiertos. [Educación JMU](https://educ.jmu.edu/~duceyje/undergrad/2022/sherwocj_project.pdf?utm_source=chatgpt.com)
7. Y aquí entra Chandler–Sin–Xiang
Hay una posible fuente de confusión muy interesante.
Chandler, Sin y Xiang publicaron en 2017:
D. Chandler, P. Sin, Q. Xiang, “The Smith group of the hypercube graph”, Designs, Codes and Cryptography 84 (2017), 283–294.
Ellos calcularon la Smith group de la matriz de adyacencia del hipercubo, es decir, la SNF de $`A`$, no directamente la SNF del laplaciano $`nI-A`$. [arXiv](https://arxiv.org/abs/1511.00272?utm_source=chatgpt.com)
Y esto es muy importante:

```math
\mathrm{SNF}(A) \neq \mathrm{SNF}(nI-A).
```

Saber completamente una de ellas no resuelve automáticamente la otra.
De hecho, el trabajo de Chandler–Sin–Xiang es un buen ejemplo de por qué el problema es traicionero: incluso con toda la maquinaria de asociación/Hamming scheme y matrices de inclusión, la aritmética integral relevante para el laplaciano no queda automáticamente controlada. [Facultad de Ciencias y Ingeniería](https://www-users.cse.umn.edu/~reiner/REU/REU2016notes/ChandlerSinXiang.pdf?utm_source=chatgpt.com)
8. ¿Qué han conseguido los trabajos más recientes?
Aquí la historia se vuelve mucho más interesante.
Gao, Marx-Kuo, McDonald y Yuen estudiaron los grupos de pila de los grafos de Cayley de

```math
\mathbb F_2^r,
```

incluido el hipercubo.
Su artículo:
J. Gao, J. Marx-Kuo, V. McDonald, C. H. Yuen, “Sandpile Groups of Cayley Graphs of $`\mathbb F_2^r`$”, Communications in Algebra (versión actualizada 2024).
se centra explícitamente en la parte $`2`$-Sylow, que describen como pobremente entendida. [arXiv](https://arxiv.org/abs/1912.06919?utm_source=chatgpt.com)
Obtuvieron, entre otras cosas:
   * número de factores cíclicos $`2`$-primarios en situaciones genéricas;
   * cotas para los casos no genéricos;
   * una cota óptima para el mayor factor $`2`$-primario;
   * para $`Q_n`$, fórmulas exactas para los $`n-1`$ factores $`2`$-primarios más grandes. [arXiv](https://arxiv.org/abs/1912.06919?utm_source=chatgpt.com)
Eso es un avance considerable.
Pero fíjate en la frase clave:
los $`n-1`$ mayores, no todos.
Y ahí está el muro.
9. ¿Dónde está exactamente el muro matricial?
Supongamos que quieres obtener la parte $`2`$-primaria de la SNF.
Una manera de verlo es que necesitas saber, para cada $`k`$,

```math
\#\{i:\;v_2(d_i)\ge k\}.
```

Equivalentemente, tienes que entender las dimensiones/rangos de determinadas reducciones módulo

```math
2,\;4,\;8,\;16,\ldots
```

No basta con calcular

```math
\mathrm{rank}(L\bmod2).
```

Eso sólo te dice esencialmente cuántos factores tienen exactamente una cierta profundidad inicial.
Para distinguir

```math
2,\;4,\;8,\;16,\ldots
```

necesitas levantar la información repetidamente por las capas

```math
\mathbb Z/2 \leftarrow \mathbb Z/4 \leftarrow \mathbb Z/8 \leftarrow \cdots.
```

Y aquí ocurre algo perverso:
módulo $`2`$
el hipercubo se vuelve extremadamente degenerado.
Como $`L=nI-A`$, dependiendo de la paridad de $`n`$,

```math
L\bmod2
```

puede comportarse esencialmente como $`A`$ o $`I+A`$, y la estructura del grupo de álgebra de $`(C_2)^n`$ adquiere una gran cantidad de nilpotencia.
Pero al pasar a

```math
\bmod 4,\quad\bmod8,\quad\bmod16,
```

parte de esa degeneración se levanta de formas que dependen de:
   * $`n\bmod 2^r`$;
   * valuaciones de coeficientes binomiales;
   * cancelaciones entre distintos niveles;
   * extensiones entre submódulos;
   * y la estructura integral de los espacios de pesos.
No hay una diagonalización simultánea sencilla que preserve toda esa información.
10. Una metáfora bastante buena
Imagina que racionalmente el hipercubo te da un edificio con plantas perfectamente separadas:

```math
0,\quad2,\quad4,\quad6,\quad\ldots,2n.
```

Espectro:
"Aquí están las plantas."
La SNF pregunta:
"¿Cómo están conectadas las escaleras cuando sólo puedes mover muebles usando operaciones enteras de determinante $`\pm1`$?"
Para $`p`$ impar, puedes utilizar $`2^{-1}`$ y buena parte de la arquitectura se separa.
Para $`p=2`$,

```math
2^{-1}
```

no existe.
Las plantas empiezan a fusionarse algebraicamente.
Y los ascensores tienen botones etiquetados por

```math
v_2\binom nk,
```

que dependen de los acarreos binarios.
Eso es mucho más difícil que conocer las alturas de las plantas.
11. Entonces, ¿es "un muro insuperable para una IA"?
Aquí te diría algo distinto de lo que probablemente esperas.
No lo llamaría insuperable.
Pero tampoco diría:
"Claro, una IA puede resolverlo si le das suficiente fuerza bruta."
Eso sería humo.
Hay tres niveles completamente distintos.
Nivel 1 — calcular casos
Esto sí está al alcance de un investigador independiente + IA.
Podemos construir algoritmos que calculen exactamente la SNF para $`n`$ moderados, estudiar los exponentes $`2`$-ádicos y buscar patrones.
Eso ya es terreno muy viable.
Nivel 2 — formular la conjetura correcta
También es muy viable.
De hecho, aquí puede estar una de las contribuciones más interesantes de una colaboración humano–IA:

```math
n=3,4,5,\ldots,100,\ldots
```

→ calcular

```math
(e_1(n),e_2(n),\ldots)
```

donde

```math
\mathrm{Syl}_2 K(Q_n) \cong \bigoplus_j\mathbb Z/2^{e_j(n)}.
```

Después buscar estructura en los $`e_j(n)`$.
Especialmente mirar:

```math
e_j(n)-e_{j+1}(n),
```

sus dependencias en

```math
v_2(n),\quad v_2(n-1),\quad s_2(n),
```

y en los acarreos binarios.
Eso es precisamente el tipo de terreno donde una IA puede ser muy buena como detector de patrones y generador de conjeturas.
Nivel 3 — demostrar la fórmula universal
Aquí está el verdadero Everest.
Porque encontrar una secuencia bonita no demuestra nada.
Hay que explicar por qué las extensiones $`2`$-ádicas de todas las capas tienen exactamente esa estructura.
Y eso probablemente requiere una idea nueva, no simplemente más potencia computacional.
12. Pero hay algo que me parece especialmente prometedor
La situación actual es mucho mejor que "Bai dejó un problema completamente virgen".
Tenemos ya varias piezas:

```math
\boxed{ \text{espectro} + \text{estructura de Cayley} + \text{álgebra de grupo} + \text{representación} + \text{valuaciones binarias} + \text{muchos factores superiores conocidos} }
```

El trabajo de Gao et al. demuestra que se puede atacar el problema desde una perspectiva algebraica mucho más fina que "calculemos una matriz gigante". [arXiv](https://arxiv.org/abs/1912.06919?utm_source=chatgpt.com)
Y eso cambia mi valoración.
13. Mi evaluación honesta para un independiente + IA
Si me preguntas:
¿Puede Rafa, sin ser matemático profesional, dirigir una IA para intentar resolverlo?
Sí.
Si me preguntas:
¿Puede hacerlo mediante fuerza bruta?
No. El crecimiento de $`Q_n`$ hace que la matriz tenga $`2^n`$ filas/columnas y la fuerza bruta muera muy pronto.
Si me preguntas:
¿Puede descubrir una conjetura nueva que los matemáticos no tengan?
Sí, me parece perfectamente plausible.
Si me preguntas:
¿Puede descubrir una demostración completa?
También sí es posible, pero aquí pondría una probabilidad mucho menor. No porque "la IA no pueda hacer matemáticas", sino porque este problema parece necesitar una estructura conceptual que todavía no está identificada.
Y ésa es justamente la diferencia entre un problema computacional y uno estructural.
Y hay una oportunidad especialmente interesante
Yo no empezaría intentando calcular directamente

```math
\mathrm{SNF}(\widetilde L_{Q_n}).
```

Intentaría algo más agresivo:

```math
\boxed{ \text{reformular el }2\text{-primary component como un problema de módulos sobre } \mathbb Z_2[(C_2)^n] }
```

y después estudiar la filtración

```math
J\supset J^2\supset J^3\supset\cdots
```

del ideal de aumento, porque módulo $`2`$

```math
J = (x_1-1,\ldots,x_n-1)
```

se vuelve esencialmente una álgebra truncada por

```math
(x_i-1)^2=0.
```

Eso convierte el fenómeno que parece una monstruosa SNF de tamaño $`2^n`$ en una pregunta sobre filtraciones, nilpotencia y extensiones $`2`$-ádicas.
Y ahí es donde yo buscaría el "puente" que todavía falta.
De hecho, el propio enfoque moderno ya apunta en esa dirección: Gao et al. utilizan una estructura natural de anillo proveniente de representación y técnicas $`2`$-ádicas para atacar los factores que permanecen inaccesibles. [arXiv](https://arxiv.org/abs/1912.06919?utm_source=chatgpt.com)
Mi veredicto: no es un muro insuperable para una IA. Es un muro de estructura. Y eso es precisamente el tipo de muro en el que una estrategia humano–IA puede tener una oportunidad real: no intentar ser más rápida que la literatura, sino encontrar una representación del problema en la que la parte $`2`$ deje de parecer una SNF monstruosa y revele qué mecanismo genera los exponentes $`2`$-ádicos.
Y si ese mecanismo aparece, entonces sí estaríamos hablando de una posible solución universal, no simplemente de otro récord computacional.

### Claude

**Qué es.** Imagina el hipercubo $Q_n$ como $2^n$ casillas, cada una conectada con $n$ vecinas. Echas granos de arena; cuando una casilla acumula $n$ granos o más, se desborda y reparte uno a cada vecina. Hay un conjunto de configuraciones "estables recurrentes" que, sumadas grano a grano y dejando desbordar, forman un grupo finito: el grupo de pila de arena. Algebraicamente es la parte de torsión del cokernel del laplaciano $L = nI - A$, y su estructura exacta se lee en la forma normal de Smith (SNF) de $L$. El tamaño total se conoce de siempre por Kirchhoff, porque los autovalores de $L$ son $2k$ con multiplicidad $\binom{n}{k}$. El tamaño es fácil. Lo difícil es cómo se reparte ese tamaño en piezas cíclicas.

**Por qué los primos impares salen y el 2 no.** Los autovalores se separan con la transformada de Walsh–Hadamard, una matriz de $\pm1$ cuyo determinante es una potencia de 2. Para un primo impar $p$ esa matriz es invertible módulo $p$. Es como un tamiz que separa la arena por colores sin perder un grano: cada autovalor $2k$ aporta su trozo por separado y la respuesta sale limpia. Bai lo hizo así: demostró la estructura del p-grupo de Sylow del grupo crítico de Qn para todo primo impar p.

Con $p=2$ el tamiz se rompe por tres motivos que en el fondo son el mismo. Primero, la matriz de Hadamard deja de ser invertible, así que no puedes separar por autovalores. Segundo, todos los autovalores $2k$ son pares, y módulo 2 colapsan en uno solo; módulo 4 se juntan por parejas, y así sucesivamente. Las piezas que querías separar están todas pegadas. Tercero, en lenguaje técnico, el anillo $\mathbb{Z}_2[\mathbb{F}_2^n]$ es *local*: el primo 2 divide el orden del grupo $\mathbb{F}_2^n$, y eso te mete en teoría de representaciones modular, donde nada se descompone en sumas directas bonitas. Escrito con $y_i = x_i - 1$, el laplaciano es (salvo signo) $\sum y_i$ dentro de un anillo donde $y_i^2 = -2y_i$. Cada potencia de $y_i$ "suelta" un factor 2 que se mezcla con los demás, como acarreos en una suma que contaminan columnas vecinas. La valuación 2-ádica de cada autovalor no te dice en qué factor cíclico acaba, porque los niveles se contaminan entre sí.

**Lo que se sabe hoy.** Se sabe que el grupo tiene exactamente $2^{n-1}-1$ factores invariantes; está enunciado en el mismo trabajo de Bai: el grupo crítico de Qn tiene exactamente 2^{n−1} − 1 factores invariantes. Gao, Marx-Kuo y McDonald dieron fórmulas exactas para los n−1 mayores factores cíclicos de Sylow-2 del hipercubo. Es la "cabeza" de la lista; el resto sigue a oscuras. Un trabajo de 2022 en JMU va más lejos en el diagnóstico: ni siquiera existe todavía una conjetura sobre la forma del 2-Sylow completo. Ese es el dato clave: no es que falte la demostración, es que nadie sabe aún qué hay que demostrar.

**¿Puede un no matemático con una IA resolverlo para todo $n$?** Muro insuperable no es. Pero la probabilidad de cerrarlo entero es baja. Te separo lo factible de lo que no lo es.

Lo factible y valioso es la fase experimental. Calcular la SNF exacta de $L$ módulo potencias de 2 para tantos $n$ como permita la máquina. Las matrices son $2^n \times 2^n$, así que crecen rápido; cuál es el $n$ máximo alcanzable en tu M2 no lo sé sin medirlo. Con esos datos se trata de buscar un patrón y **formular la primera conjetura**. Eso solo ya sería una contribución publicable, porque hoy no existe.

Lo difícil es la demostración universal. Requiere teoría de representaciones modulares, filtraciones del ideal de aumentación y combinatoria 2-ádica fina. Aquí la IA es peligrosa por un motivo concreto: produce demostraciones convincentes y falsas, y tú no tienes forma independiente de auditarlas. El cruce contra datos medidos que haces en tu proyecto atrapa enunciados falsos, pero no atrapa una demostración con un hueco lógico que casualmente acierta en los $n$ medidos.

Aplicándole tu propio filtro: los datos por $n$ son una lista que crece con $n$, muerta como solución. La respuesta real tendría que ser UN enunciado con $n$ dentro, sea una fórmula o una recursión de $Q_{n-1}$ a $Q_n$. La recursión es la vía más plausible, porque $Q_n = Q_{n-1} \times K_2$ y así es como Bai atacó los primos impares. Lo que no sabe nadie es si existe una respuesta cerrada o si la estructura es intrínsecamente caótica. Que lleve más de 20 años sin conjetura sugiere que, aunque la respuesta exista, no es simple.

---

<sub>How long it took: the problem was chosen on 2 October 2026. The proof of the whole 2-part, with the fold law, was complete and read cold end to end on 5 October: about three days. Version 8 of the paper was published on 6 October.</sub>

*6 October 2026*
