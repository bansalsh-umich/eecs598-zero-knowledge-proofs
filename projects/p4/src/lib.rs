use p1::Field;
use p2::sparsemat::{SparseMatrix, SparseVector};
pub mod gadgets;

mod lc;
pub mod snark;
pub use anyhow::Result;
use anyhow::format_err;
pub use lc::Lc;

// Rust does not (yet) have trait aliases so this roundabout syntax is required to declare it, but
// Thunk<T> is just an alias for FnOnce() -> T This is basically a 'T' which is computed 'lazily'
// (i.e. only if it is actually needed)
pub trait Thunk: FnOnce() -> <Self as Thunk>::Output {
    type Output;
}
impl<F, T> Thunk for F
where
    F: FnOnce() -> T,
{
    type Output = T;
}

#[derive(Clone, Eq, PartialEq, Hash, Copy, Debug)]
/// Whether a variable belongs to the public statement or the private witness.
pub enum Visibility {
    /// This value is part of the statement.
    Public,
    /// This value is part of the witness.
    Private,
}

#[derive(Clone, Eq, Hash, Copy, PartialEq, Debug)]
/// A handle to a variable allocated by a [`ConstraintInterpreter`].
///
/// This is not the field element itself. It is the identifier used inside
/// linear combinations and constraints.
pub struct Variable(Visibility, usize);

impl Variable {
    /// Construct a variable from a visibility class and namespace-local index.
    ///
    /// In most code, variables should come from
    /// [`ConstraintInterpreter::alloc`] instead.
    pub fn new_unchecked(vis: Visibility, idx: usize) -> Self {
        Self(vis, idx)
    }

    /// Return this variable's index within its own visibility class.
    ///
    /// Public and private variables are indexed separately.
    pub fn get_index(&self) -> usize {
        self.1
    }

    /// Return whether this variable is public or private.
    pub fn visibility(&self) -> Visibility {
        self.0
    }
    /// Return the distinguished public variable representing the constant `1`.
    ///
    /// This is how a linear combination represents a constant term.
    pub fn one() -> Self {
        Self::new_unchecked(Visibility::Public, 0)
    }
}

/// Interface used by [`Circuit::synthesize`] to emit variables and constraints.
pub trait ConstraintInterpreter<F> {
    /// Allocate a fresh variable together with an optional concrete assignment.
    ///
    /// `annotation` is only for diagnostics. `vis` decides whether the variable
    /// belongs to the statement or witness. `constructor` supplies a value when
    /// the interpreter needs one.
    fn alloc(
        &mut self,
        annotation: impl Thunk<Output: AsRef<str>>,
        vis: Visibility,
        constructor: impl Thunk<Output = Option<impl Into<F>>>,
    ) -> Result<Variable>;

    /// Record one constraint of the form `a(z) * b(z) = c(z)`.
    ///
    /// The three linear combinations become one row of the final R1CS instance.
    fn enforce(&mut self, annotation: impl Thunk<Output: AsRef<str>>, a: Lc<F>, b: Lc<F>, c: Lc<F>);
}

/// A relation that can be synthesized into constraints.
///
/// Implementations allocate variables and then add constraints describing the
/// relation that should hold between them.
pub trait Circuit<F> {
    fn synthesize<I: ConstraintInterpreter<F>>(self, cs: &mut I) -> Result<()>;
}

/// A [`ConstraintInterpreter`] that records constraints in matrix form.
///
/// It stores one linear combination per row of the eventual `A`, `B`, and `C`
/// matrices. Public and private variables keep separate indices while the
/// circuit is being built; when the matrices are produced, private-variable
/// columns come after all public-variable columns.
///
/// If `IS_PROVER` is `true`, private assignments are stored so a witness can be
/// produced later. If it is `false`, only the public part of the assignment is
/// retained.
pub struct Matrixifier<F, const IS_PROVER: bool> {
    /// Rows of the `A` matrix, stored as linear combinations.
    a_rows: Vec<Lc<F>>,
    /// Rows of the `B` matrix, stored as linear combinations.
    b_rows: Vec<Lc<F>>,
    /// Rows of the `C` matrix, stored as linear combinations.
    c_rows: Vec<Lc<F>>,
    /// Number of allocated public variables, including `Variable::one()`.
    cur_pub: usize,
    /// Number of allocated private variables.
    cur_priv: usize,
    /// Known public assignments, indexed in the public namespace.
    pub_vars: Vec<(usize, F)>,
    /// Known private assignments, indexed in the private namespace.
    priv_vars: Vec<(usize, F)>,
}

pub type ProverMatrixifier<F> = Matrixifier<F, true>;
pub type VerifierMatrixifier<F> = Matrixifier<F, false>;

impl<F: Field, const IS_PROVER: bool> Default for Matrixifier<F, IS_PROVER> {
    fn default() -> Self {
        Self {
            a_rows: Default::default(),
            b_rows: Default::default(),
            c_rows: Default::default(),
            // Constraint systems start out with a variable set to the constant 1
            // This is what allows you to encode constant terms in constraints e.g.
            // 2*var_x * var_y + 7 = var_z is encoded as 2*var_x*var_y + 7*Variable::one() = var_z
            pub_vars: vec![(Variable::one().get_index(), F::one())],
            cur_pub: 1,
            cur_priv: 0,
            priv_vars: vec![],
        }
    }
}

impl<F: Field, const IS_PROVER: bool> ConstraintInterpreter<F> for Matrixifier<F, IS_PROVER> {
    /// Allocate the next variable in the requested visibility class.
    ///
    /// Add a variable to the constraint system with the prescribed visibility. If vis is Visibility::Private and IS_PROVER is
    /// false, `constructor` should not be called (the verifier would not have access to private
    /// witness values anyway).
    ///
    /// `annotation` is largely here for debug purposes, feel free to print it via e.g.
    /// println!("{}", annotation().as_ref())
    fn alloc(
        &mut self,
        annotation: impl Thunk<Output: AsRef<str>>,
        vis: Visibility,
        constructor: impl Thunk<Output = Option<impl Into<F>>>,
    ) -> Result<Variable> {
        todo!()
    }

    /// Add one multiplicative constraint to the internal row lists.
    /// As above, `annotation` here is largely for debugging purposes when writing gadgets
    fn enforce(
        &mut self,
        annotation: impl Thunk<Output: AsRef<str>>,
        a: Lc<F>,
        b: Lc<F>,
        c: Lc<F>,
    ) {
        todo!()
    }
}

// these are just convenience aliases for the return types of into_statement/into_statement_and_witness
// Statement<F> is ([A, B, C], x) and Witness<F> is w
type Statement<F> = ([SparseMatrix<F>; 3], SparseVector<F>);
type Witness<F> = SparseVector<F>;

impl<F: Field, const IS_PROVER: bool> Matrixifier<F, IS_PROVER> {
    /// Construct an empty matrixifier with the constant-one public variable
    /// already reserved at public index `0`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Export the accumulated constraints as a statement.
    ///
    /// The returned statement consists of the three sparse matrices `A`, `B`,
    /// and `C`, together with the sparse vector of public assignments.
    ///
    /// The main job here is to convert the internal row representation into the
    /// sparse-matrix form, while preserving the public/private column convention described on
    /// [`Matrixifier`].
    pub fn into_statement(self) -> Statement<F> {
        todo!()
    }
}

impl<F: Field> ProverMatrixifier<F> {
    /// Export both the public statement and the private witness assignment.
    /// (should be able to take advantage of self.into_statement())
    ///
    /// This packages the prover-facing output: the public statement together
    /// with the private assignment vector aligned with the private columns of
    /// that statement.
    pub fn into_statement_and_witness(mut self) -> (Statement<F>, Witness<F>) {
        todo!()
    }
}
