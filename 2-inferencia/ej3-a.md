# Ejercicio 3

# Empty

$W([~]) = \empty \rhd [~]_s : [s]$

# Cons

$W(U::V) = S\Gamma_1 \cup S\Gamma_2 \rhd S(M::N) : S\tau$ donde
  
- $W(U) = \Gamma_1 \rhd M:\sigma$
- $W(V) = \Gamma_2 \rhd N:\tau$
- $S = MGU\{\tau \doteq [\sigma]\} \cup \{\sigma_1 \doteq \sigma_2 \mid x:\sigma_1 \in \Gamma_1,x:\sigma_2 \in \Gamma_2\}$

# ZipWith

$W(zip~U~and~V~with~x,y \leadsto W) = \displaystyle\bigcup_{i=1}^{3}S\Gamma_i \rhd S(zip~M~and~N~with~x,y \leadsto O) : [\rho]$ donde

- $W(U) = \Gamma_1 \rhd M:\sigma$
- $W(V) = \Gamma_2 \rhd N:\tau$
- $W(W) = \Gamma_{3} \rhd O:\rho$
- $\Gamma_{3'} = \Gamma_3 \ominus \{x,\ y\}$
- $S = MGU\{\sigma \doteq [\tau_x], \tau \doteq [\tau_y]\} \cup \{\sigma_1 \doteq \sigma_2 \mid x:\sigma_1 \in \Gamma_i,x:\sigma_2 \in \Gamma_j, i,j \in \{1,2,3'\}\}$
- $\tau_y = \begin{cases}
   \beta  & si\ y:\beta \in \Gamma_3     \\
    \text{variable fresca si no}
  \end{cases} 
  $
- $\tau_x = \begin{cases}
   \alpha  & si\ x:\alpha \in \Gamma_3     \\
    \text{variable fresca si no}
  \end{cases} 
  $
