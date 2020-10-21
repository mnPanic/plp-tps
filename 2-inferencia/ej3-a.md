# Ejercicio 3

## Item a

$W([~]) = \empty \rhd [~]_s : [s]$

$W(U::V) = S\Gamma_1 \cup S\Gamma_2 \rhd S(M::N) : S\tau$ donde
  
- $W(U) = \Gamma_1 \rhd M:\sigma$
- $W(V) = \Gamma_2 \rhd N:\tau$
- $S = MGU\{\tau \doteq [\sigma]\} \cup \{\sigma_1 \doteq \sigma_2 \mid x:\sigma_1 \in \Gamma_1,x:\sigma_2 \in \Gamma_2\}$

$W(zip~U~and~V~with~x,y \leadsto W) = \displaystyle\bigcup_{i=1}^{3}S\Gamma_i \rhd S(zip~M~and~N~with~x,y \leadsto O) : [\rho]$ donde

- $W(U) = \Gamma_1 \rhd M:\sigma$
- $W(V) = \Gamma_2 \rhd N:\tau$
- $W(W) = \{\Gamma_3, x:s_0, y:s_1\} \rhd O:\rho$
- $S = MGU\{\sigma \doteq [s_1], \tau \doteq [s_2]\} \cup \{\sigma_1 \doteq \sigma_2 \mid x:\sigma_1 \in \Gamma_i,x:\sigma_2 \in \Gamma_j, i\neq j\}$
