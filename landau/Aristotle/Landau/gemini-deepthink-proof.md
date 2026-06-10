Here is the precise, mathematically rigorous formulation and detailed proof of the steady-state classification theorem for the non-electrostatic **Vlasov-Maxwell-Landau (VML)** system.

To ensure there is absolutely no mathematical hand-waving, we explicitly state the topology of the domain, the functional spaces, and the exact asymptotic tail bounds on the distribution function. These strict conditions are mandatory to rigorously justify integration by parts in unbounded phase space, the absolute convergence of fluid moments, and the well-posedness of the entropy dissipation functional.

---

### **I. Mathematical Formulation and Theorem Statement**

#### **1. The Domain and Equations**

* **Spatial Domain:** The three-dimensional flat torus $\mathbb{T}^3 = (\mathbb{R}/L\mathbb{Z})^3$ for a given $L > 0$, representing a periodic domain without physical boundaries.
* **Velocity Domain:** The entire Euclidean space $\mathbb{R}^3$.
* **Phase Space:** $\Omega = \mathbb{T}^3 \times \mathbb{R}^3$.
* **Physical Constants:** Particle mass $m > 0$, charge $q \neq 0$, vacuum permittivity $\varepsilon_0 > 0$, vacuum permeability $\mu_0 > 0$.
* **Background:** A stationary, spatially uniform neutralizing background of charge density $-q n_{bg}$ (with $n_{bg} > 0$).

The steady-state (time-independent) Vlasov-Maxwell-Landau system for the particle distribution function $f(x,v) \ge 0$ and the self-consistent macroscopic electromagnetic fields $E(x), B(x)$ is:

**Vlasov-Landau Equation:**


$$ v \cdot \nabla_x f + \frac{q}{m} \big( E(x) + v \times B(x) \big) \cdot \nabla_v f = Q_L(f, f) $$

**Maxwell's Equations:**


$$ \nabla_x \times E = 0 \quad \text{(Faraday)} $$

$$ \nabla_x \cdot E = \frac{q}{\varepsilon_0} \left( \int_{\mathbb{R}^3} f(x,v) \, dv - n_{bg} \right) \quad \text{(Gauss)} $$

$$ \nabla_x \times B = \mu_0 q \int_{\mathbb{R}^3} v f(x,v) \, dv \quad \text{(Ampere)} $$

$$ \nabla_x \cdot B = 0 \quad \text{(Gauss-Magnetic)} $$

The **Landau collision operator** for Coulomb interactions is defined in divergence form as:


$$ Q_L(f,f)(x,v) = c_L \sum_{i,j=1}^3 \frac{\partial}{\partial v_i} \int_{\mathbb{R}^3} A_{ij}(v - v') \left[ f(x,v') \frac{\partial f(x,v)}{\partial v_j} - f(x,v) \frac{\partial f(x,v')}{\partial v'_j} \right] dv' $$


where $c_L > 0$ is a collisional constant and $A(z) = \frac{1}{|z|} \left( \mathbf{I}_{3\times 3} - \frac{z \otimes z}{|z|^2} \right)$ is the non-negative projection matrix onto the orthogonal complement of $z$.

#### **2. Rigorous Hypotheses on the Solutions**

Let $(f, E, B)$ be a classical steady-state solution. We impose the following strict analytical assumptions:

* **(H1) Classical Regularity:** The electromagnetic fields are continuously differentiable: $E, B \in C^1(\mathbb{T}^3; \mathbb{R}^3)$. The distribution function is smooth enough for the transport and collision operators to be strongly defined pointwise: $f \in C^1(\Omega; \mathbb{R})$ and its second velocity derivatives exist and are continuous: $\nabla_v^2 f \in C^0(\Omega; \mathbb{R})$.
* **(H2) Strict Positivity and Gaussian Lower Bound:** To ensure the entropy density $\ln f$ is globally well-defined without vacuum singularities, $f$ is strictly positive and bounded below by a Maxwellian. There exist constants $c_0 > 0$ and $\beta_0 > 0$ such that:

$$ f(x,v) \ge c_0 e^{-\beta_0 |v|^2} > 0 \quad \forall (x,v) \in \Omega $$



*(Consequence: This ensures $|\ln f(x,v)| \le |\ln c_0| + \beta_0 |v|^2$, strictly limiting its growth as $|v| \to \infty$).*
* **(H3) Rapid Decay (Gaussian Upper Tail Bounds):** To guarantee that all moments converge absolutely and boundary flux terms at $|v| \to \infty$ strictly vanish, $f$ and its gradients are bounded above by a Gaussian. There exist constants $c_1 > 0$ and $\beta_1 > 0$ such that:

$$ f(x,v) + |\nabla_x f(x,v)| + |\nabla_v f(x,v)| + |\nabla_v^2 f(x,v)| \le c_1 e^{-\beta_1 |v|^2} \quad \forall (x,v) \in \Omega $$


* **(H4) Global Charge Neutrality:** The total number of particles matches the background: $\iint_{\Omega} f(x,v) \, dv \, dx = n_{bg} |\mathbb{T}^3|$.

#### **3. Statement of the Theorem**

Under hypotheses (H1)–(H4), any steady-state solution to the Vlasov-Maxwell-Landau system takes the form of a spatially uniform, zero-drift global Maxwellian:


$$ f(x,v) = n_{bg} \left( \frac{m}{2\pi k_B T_0} \right)^{3/2} \exp\left( - \frac{m|v|^2}{2 k_B T_0} \right) $$


for some constant temperature $T_0 > 0$. Concurrently, the macroscopic fields are restricted to:


$$ E(x) \equiv 0, \quad B(x) \equiv B_0 $$


where $B_0 \in \mathbb{R}^3$ is an arbitrary constant vector.

---

### **II. Detailed, Rigorous Proof**

#### **Step 1: Global Entropy Dissipation**

Because $f > 0$ strictly (H2), the function $\ln f$ is well-defined and $C^1$. We multiply the Vlasov-Landau equation by $\ln f$ and integrate over the entire phase space $\Omega$:


$$ \iint_{\Omega} \Big[ v \cdot \nabla_x f + \frac{q}{m} (E + v \times B) \cdot \nabla_v f \Big] \ln f \, dv \, dx = \iint_{\Omega} Q_L(f,f) \ln f \, dv \, dx $$

We analyze the left-hand side using the identity $\nabla(f \ln f - f) = \ln f \nabla f$:

1. **Spatial transport term:** $\iint \nabla_x \cdot \big[v (f \ln f - f)\big] dv dx$.
By (H3), the integral converges absolutely, allowing us to swap the integrals via Fubini's theorem. By the Divergence Theorem on the boundaryless torus $\mathbb{T}^3$, the spatial integral evaluates to exactly $0$.
2. **Lorentz force term:** $\frac{q}{m} \iint \nabla_v \cdot \big[(E + v \times B)(f \ln f - f)\big] dx dv$.
Here, we utilized the product rule $\nabla_v \cdot (F \psi) = (\nabla_v \cdot F)\psi + F \cdot \nabla_v \psi$, and noted that $\nabla_v \cdot E = 0$ and $\nabla_v \cdot (v \times B) = B \cdot (\nabla_v \times v) - v \cdot (\nabla_v \times B) = 0$.
For a fixed $x$, we apply the Divergence Theorem in velocity space over the ball $|v| \le R$ and take the limit $R \to \infty$. The boundary flux is:

$$ \lim_{R \to \infty} \oint_{|v|=R} \Big( (E + v \times B) \cdot \frac{v}{|v|} \Big) (f \ln f - f) \, dS_R $$



Because $(v \times B) \cdot v \equiv 0$, the magnetic term drops out of the boundary flux entirely. We are left with $(E \cdot \frac{v}{|v|})(f \ln f - f)$. Since $E(x)$ is continuous on the compact torus, it is uniformly bounded. By (H2), $|\ln f|$ grows at most quadratically. By (H3), $f$ decays exponentially. The product $|v|^2 e^{-\beta_1 |v|^2}$ goes to zero far faster than the surface area $4\pi R^2$ grows. Thus, the velocity boundary term rigorously evaluates to zero.

The entire left-hand side is zero. We are left with the global entropy dissipation equation:


$$ \int_{\mathbb{T}^3} D_L(f)(x) \, dx = 0, \quad \text{where} \quad D_L(f)(x) = \int_{\mathbb{R}^3} Q_L(f,f) \ln f \, dv $$

#### **Step 2: The H-Theorem and the Local Maxwellian**

We express $D_L(f)$ in its symmetric weak form. Thanks to the rapid decay provided by (H3), we can rigorously integrate by parts in $v$ to move the velocity derivative onto $\ln f$. Symmetrizing the variables $v$ and $v'$, and noting that $A_{ij}(z)$ is an even function, we obtain:


$$ D_L(f)(x) = -\frac{c_L}{2} \iint_{\mathbb{R}^3 \times \mathbb{R}^3} f(v)f(v') \sum_{i,j=1}^3 A_{ij}(v-v') W_i W_j \, dv \, dv' $$


where $W = \nabla_v \ln f(v) - \nabla_{v'} \ln f(v')$.
Because $A(z)$ is a positive semi-definite matrix, the integrand is strictly non-negative. Therefore, $D_L(f)(x) \le 0$ pointwise in $x$. Since the integral of a non-positive continuous function over $\mathbb{T}^3$ is zero, we must have $D_L(f)(x) \equiv 0$ everywhere.

For the integrand to vanish almost everywhere, the vector $W$ must lie in the null space of $A(v-v')$. Since $A(z)$ is the projection matrix onto the orthogonal complement of $z$, its null space is precisely the span of $z$. Therefore, there exists a scalar function $\lambda(x,v,v')$ such that:


$$ \nabla_v \ln f(x,v) - \nabla_{v'} \ln f(x,v') = \lambda(x,v,v') (v - v') $$


Taking the curl of both sides with respect to $v$ yields $\nabla_v \times (\lambda (v-v')) = \nabla_v \lambda \times (v-v') = 0$, meaning $\nabla_v \lambda$ is parallel to $(v-v')$. By symmetry, $\nabla_{v'} \lambda$ is also parallel to $(v-v')$, which implies $\lambda$ depends only on the distance $|v-v'|$.
Differentiating the original relation with respect to $v_j$ yields:


$$ \partial^2_{v_i v_j} \ln f(v) = \partial_{v_j} \big[ \lambda (|v-v'|) (v_i - v'_i) \big] $$


Because the left-hand side is strictly independent of $v'$, the right-hand side must also be independent of $v'$. Evaluating the right side at the limit $v' \to v$ forces the derivative to collapse to $\lambda(x, 0) \delta_{ij}$.
Therefore, the Hessian matrix of $\ln f$ is a scalar multiple of the identity, meaning $\ln f$ is a quadratic polynomial in $v$:


$$ \ln f(x,v) = a(x) + \sum_{i=1}^3 b_i(x) v_i + c(x) |v|^2 $$


To satisfy the integrability requirement (H3), $c(x)$ must be strictly negative. Mapping these to macroscopic fields $n(x), u(x), T(x)$, we have rigorously proven that $f$ is a **local Maxwellian**.

#### **Step 3: Vlasov Kinematics via Polynomial Matching**

Since $f$ is a local Maxwellian, $Q_L(f,f) \equiv 0$. The Vlasov equation simplifies to purely collisionless transport. Dividing by $f$ yields:


$$ v \cdot \nabla_x (\ln f) + \frac{q}{m} (E + v \times B) \cdot \nabla_v (\ln f) = 0 $$


Substitute $\ln f = a + b \cdot v + c|v|^2$ and compute the gradients:

* $\nabla_x \ln f = \nabla_x a + (\nabla_x b)^T v + (\nabla_x c)|v|^2$
* $\nabla_v \ln f = b + 2cv$

Substitute these into the Vlasov equation. Note that $(v \times B) \cdot v \equiv 0$ and $(v \times B) \cdot b = v \cdot (B \times b)$. Grouping by homogeneous powers of $v$ yields:


$$ \left( \sum_{j=1}^3 v_j \partial_{x_j} c \right) |v|^2 + \sum_{i,j=1}^3 v_i v_j \partial_{x_j} b_i + \sum_{j=1}^3 v_j \left( \partial_{x_j} a + \frac{2qc}{m} E_j + \frac{q}{m}(B \times b)_j \right) + \frac{q}{m} E \cdot b = 0 $$


By (H1), the fields $a,b,c$ are classically differentiable. Because $x$ and $v$ are completely independent variables, this 3rd-degree polynomial must evaluate to zero for *all* $v \in \mathbb{R}^3$. Therefore, by linear independence, the tensor coefficient of every homogeneous degree of $v$ must identically vanish.

#### **Step 4: Restricting the Macroscopic Coefficients**

1. **$\mathcal{O}(|v|^3)$ Terms:** $\nabla_x c = 0$. Since $c = -m/(2k_B T)$, the **temperature $T(x) = T_0$ is a global constant.**
2. **$\mathcal{O}(|v|^2)$ Terms:** $\sum_{i,j} v_i v_j \partial_{x_j} b_i = 0$. Since $v_i v_j$ is a symmetric tensor, the symmetric part of the Jacobian of $b$ must vanish:

$$ \partial_{x_i} b_j + \partial_{x_j} b_i = 0 \quad \text{(Killing's Equation)} $$



To find its solutions on the periodic torus $\mathbb{T}^3$, we integrate the sum of squares:

$$ 0 = \int_{\mathbb{T}^3} \sum_{i,j} (\partial_{x_i} b_j + \partial_{x_j} b_i)^2 dx = 2 \int_{\mathbb{T}^3} \sum_{i,j} (\partial_{x_i} b_j)^2 dx + 2 \int_{\mathbb{T}^3} \sum_{i,j} (\partial_{x_i} b_j)(\partial_{x_j} b_i) dx $$



Integrating the cross-term by parts:

$$ \int_{\mathbb{T}^3} \sum_{i,j} \partial_{x_i} b_j \partial_{x_j} b_i dx = - \int_{\mathbb{T}^3} \sum_{i,j} b_j \partial_{x_i} \partial_{x_j} b_i dx = \int_{\mathbb{T}^3} \sum_{i,j} \partial_{x_j} b_j \partial_{x_i} b_i dx = \int_{\mathbb{T}^3} (\nabla_x \cdot b)^2 dx $$



Setting $i=j$ in Killing's equation yields $2\partial_{x_i} b_i = 0 \implies \nabla_x \cdot b = 0$. Thus, the cross-term integral vanishes, leaving:

$$ 2 \int_{\mathbb{T}^3} \sum_{i,j} (\partial_{x_i} b_j)^2 dx = 0 \implies \partial_{x_i} b_j = 0 \quad \forall i,j $$



Thus, $b(x) = b_0$ is a constant vector. Since $b = mu/(k_B T_0)$, the **bulk drift velocity $u(x) = u_0$ is a global constant.**
3. **$\mathcal{O}(|v|^1)$ Terms:** With $T_0$ and $u_0$ constant, $a(x) = \ln n(x) + \text{const}$, so $\nabla_x a = \nabla_x \ln n$. Substituting $c$ and $b$ yields the macroscopic force balance:

$$ \nabla_x \ln n = \frac{q}{k_B T_0} (E + u_0 \times B) $$


4. **$\mathcal{O}(|v|^0)$ Term:** $\frac{q}{m} E \cdot b_0 = 0 \implies E \cdot u_0 = 0$.

#### **Step 5: Ampere's Law and the Nullification of Bulk Velocity**

The macroscopic current is $J(x) = q \int v f \, dv = q n(x) u_0$. Ampere's Law dictates $\nabla_x \times B = \mu_0 q n(x) u_0$.
Take the dot product of both sides with the constant vector $u_0$:


$$ u_0 \cdot (\nabla_x \times B) = \mu_0 q n(x) |u_0|^2 $$


Using the vector identity $\nabla_x \cdot (B \times u_0) = u_0 \cdot (\nabla_x \times B) - B \cdot (\nabla_x \times u_0)$ and noting $\nabla_x \times u_0 = 0$, we have:


$$ \nabla_x \cdot (B \times u_0) = \mu_0 q n(x) |u_0|^2 $$


Integrate this exact divergence over the periodic torus $\mathbb{T}^3$. By the Divergence Theorem, the LHS evaluates to exactly zero:


$$ 0 = \mu_0 q |u_0|^2 \int_{\mathbb{T}^3} n(x) \, dx $$


By (H2), $f>0$, so the physical density $n(x) > 0$. Therefore, $\int n(x) dx > 0$. Since $\mu_0 > 0$ and $q \neq 0$, the equality strictly demands $|u_0| = 0$.
**Result:** The bulk velocity vanishes everywhere, $u_0 = 0$.

#### **Step 6: Faraday, Gauss, and the Poisson-Boltzmann Equation**

With $u_0 = 0$, the $\mathcal{O}(|v|^1)$ force-balance relation reduces to purely electrostatic equilibrium:


$$ \nabla_x \ln n = \frac{q}{k_B T_0} E $$


From Faraday's Law, $\nabla_x \times E = 0$. By the Hodge Decomposition theorem on the torus $\mathbb{T}^3$, any curl-free vector field can be written as $E = -\nabla_x \phi + E_{harm}$, where $E_{harm}$ is a constant harmonic vector. Thus:


$$ \nabla_x \ln n = -\frac{q}{k_B T_0} \nabla_x \phi + \frac{q}{k_B T_0} E_{harm} $$


If we integrate this equation along any fundamental closed cycle $\gamma$ of the torus, the integrals of the exact gradients $\nabla \ln n$ and $\nabla \phi$ are exactly zero by periodicity. We are left with $0 = \frac{q}{k_B T_0} E_{harm} \cdot \oint_{\gamma} dl$, which strictly forces the constant vector $E_{harm} = 0$. Therefore, $E = -\nabla_x \phi$ globally.

Integrating the remaining gradient equation yields the Boltzmann density relation:


$$ n(x) = C_0 \exp\left(-\frac{q\phi(x)}{k_B T_0}\right) $$


where $C_0 > 0$. We substitute this into Gauss's Law ($-\Delta_x \phi = \frac{q}{\varepsilon_0}(n - n_{bg})$):


$$ -\Delta_x \phi = \frac{q}{\varepsilon_0} \left( C_0 e^{-\frac{q\phi(x)}{k_B T_0}} - n_{bg} \right) $$


For a solution to exist on a periodic torus, the net charge must be zero: $\int (n(x) - n_{bg}) dx = 0$. By the Mean Value Theorem for integrals, there must exist a reference potential $\phi_0$ such that $C_0 e^{-q\phi_0 / k_B T_0} = n_{bg}$. Let $\psi(x) = \frac{q}{k_B T_0}(\phi(x) - \phi_0)$. The PDE simplifies to the nonlinear Poisson-Boltzmann equation:


$$ -\Delta_x \psi = \frac{q^2 n_{bg}}{\varepsilon_0 k_B T_0} \left( e^{-\psi(x)} - 1 \right) $$


Multiply by $\psi$ and integrate over $\mathbb{T}^3$. Applying integration by parts yields:


$$ \int_{\mathbb{T}^3} |\nabla_x \psi|^2 \, dx = \frac{q^2 n_{bg}}{\varepsilon_0 k_B T_0} \int_{\mathbb{T}^3} \psi \left( e^{-\psi(x)} - 1 \right) \, dx $$


Examine the algebraic sign of the right-hand integrand $\psi (e^{-\psi} - 1)$. For any real $\psi \neq 0$, the quantities $\psi$ and $(e^{-\psi} - 1)$ have strictly opposite signs, making their product strictly negative. Thus, the right-hand integral is $\le 0$. However, the left-hand integral of a squared gradient is $\ge 0$. They can only satisfy the equality if both sides are exactly $0$.
This implies $\nabla_x \psi = 0$, meaning $\psi$ is constant. For the RHS to be zero, that constant must be exactly $\psi = 0$.
**Result:** $\phi(x)$ is a global constant. Consequently, the electric field vanishes ($E \equiv 0$) and the density is uniform ($n(x) \equiv n_{bg}$).

#### **Step 7: Harmonicity of the Magnetic Field**

Because $u_0 = 0$, the macroscopic current $J$ vanishes. Ampere's Law reduces to $\nabla_x \times B = 0$. Coupled with the monopole constraint $\nabla_x \cdot B = 0$, we evaluate the vector Laplacian:


$$ \Delta_x B = \nabla_x (\nabla_x \cdot B) - \nabla_x \times (\nabla_x \times B) = 0 $$


Because each Cartesian component of $B$ is a harmonic function on the compact manifold $\mathbb{T}^3$, the Maximum Principle dictates that each component is a global constant.
**Result:** The magnetic field is a uniform constant vector $B(x) \equiv B_0$.

#### **Conclusion**

All kinematic and electromagnetic constraints of the Vlasov-Maxwell-Landau system have been rigidly exhausted. The spatial dependencies have collapsed, leaving $T(x) = T_0$, $n(x) = n_{bg}$, and $u(x) = 0$. Substituting these parameters back into the local Maxwellian derived in Step 2 perfectly yields the spatially uniform, zero-drift global Maxwellian. $\hfill \blacksquare$