//! # Interactive Proofs
//!
//! This module provides the infrastructure for implementing interactive proof protocols where
//! a prover and verifier exchange messages. The key abstraction is the [`InteractiveProof`] trait
//! which you will implement for each protocol (sumcheck, polynomial commitment, etc.).
//!
//! ## Quick Start
//!
//! To implement an interactive proof:
//! 1. Define your statement type (public inputs known to both parties)
//! 2. Define your witness type (private inputs known only to the prover)
//! 3. Define the message types exchanged between prover and verifier
//! 4. Implement the `prover` and `verifier` async functions
//!
//! ## The Comms Struct: Communication Between Prover and Verifier
//!
//! The [`Comms`] struct is how the prover and verifier talk to each other. Think of it as a
//! two-way communication channel. Here are the key methods you will use:
//!
//! ### `send(msg)` - Send a message to the other party
//!
//! ```ignore
//! comms.send(MyMessage::SomeVariant(data))?;
//! ```
//!
//! This sends a message and returns immediately. The `?` propagates any errors (e.g., if the
//! channel is closed because the other party crashed).
//!
//! ### `recv().await` - Receive a message from the other party
//!
//! ```ignore
//! let msg = comms.recv().await?;
//! ```
//!
//! This waits until a message arrives from the other party. The `.await` is required because
//! this is an async operation that may need to wait. The `?` propagates errors (e.g., timeout
//! or channel closed).
//!
//! ### `establish_subprotocol(name).await` - Create a channel for a nested protocol
//!
//! ```ignore
//! let sub_comms: Comms<SubProverMsg, SubVerifierMsg> =
//!     comms.establish_subprotocol("inner_protocol").await?;
//! ```
//!
//! When your protocol needs to run another protocol as a subroutine (e.g., delphian calling
//! a polynomial commitment), use this to create a new communication channel with different
//! message types. The type parameters specify what messages the subprotocol will exchange.
//!
//! ## CRITICAL: Matching Call Sequences
//!
//! **The prover and verifier must make matching send/recv calls in the same order, or the
//! protocol will deadlock (hang forever).**
//!
//! For example, if the prover does:
//! ```ignore
//! comms.send(msg1)?;           // Step 1: prover sends
//! let r = comms.recv().await?; // Step 2: prover waits to receive
//! ```
//!
//! Then the verifier MUST do:
//! ```ignore
//! let m = comms.recv().await?; // Step 1: verifier waits to receive
//! comms.send(challenge)?;      // Step 2: verifier sends
//! ```
//!
//! If both parties try to `recv` at the same time, the protocol will hang.
//! Similarly, `establish_subprotocol` calls must happen
//! at the same point in both the prover and verifier code with matching identifiers.
//!
//! ## A Note on Async Functions
//!
//! You will see the `async` keyword on the prover and verifier functions. For this project,
//! you only need to know two things:
//!
//! 1. When calling an async function or method (like `recv()`), add `.await` after the call
//! 2. You can use `?` for error handling just like in normal functions
//!
//! The async machinery handles running the prover and verifier concurrently so they can
//! exchange messages. You do not need to understand how this works internally.
//!
//! ## Debugging: Viewing the Transcript
//!
//! When running tests, you can see the full transcript of messages exchanged between the
//! prover and verifier by using the `--nocapture` flag:
//!
//! ```bash
//! cargo test my_test_name -- --nocapture
//! ```
//!
//! To filter the transcript and only see certain messages, set the `TRANSCRIPT_FILTER`
//! environment variable:
//!
//! ```bash
//! # Only see prover messages (both sent and received)
//! TRANSCRIPT_FILTER=prover cargo test my_test_name -- --nocapture
//!
//! # Only see messages the prover sends
//! TRANSCRIPT_FILTER=prover,send cargo test my_test_name -- --nocapture
//!
//! # Only see messages the prover receives
//! TRANSCRIPT_FILTER=prover,recv cargo test my_test_name -- --nocapture
//!
//! # Same options work for verifier
//! TRANSCRIPT_FILTER=verifier cargo test my_test_name -- --nocapture
//! TRANSCRIPT_FILTER=verifier,send cargo test my_test_name -- --nocapture
//! TRANSCRIPT_FILTER=verifier,recv cargo test my_test_name -- --nocapture
//! ```

// Silences compiler warning that isn't relevant to our use case.
#![expect(async_fn_in_trait)]
pub use comms::{Comms, Party};
use rand::Rng;
use std::{fmt::Debug, pin::pin};

/// The result type used throughout this crate, powered by the `anyhow` library.
///
/// `anyhow::Result<T>` is just an alias for `std::result::Result<T, anyhow::Error>`. The
/// `anyhow::Error` type can hold any error type, so you do not need to define custom error
/// types or worry about converting between different error types.
///
/// ## Error Handling with Anyhow
///
/// ### The `?` Operator (Rust built-in, not anyhow-specific)
///
/// The `?` operator is a standard Rust feature for propagating errors. If an operation returns
/// `Result<T, E>`, adding `?` will either unwrap the success value or return early with the
/// error:
///
/// ```ignore
/// let value = some_fallible_operation()?; // Returns early if error
/// ```
///
/// Anyhow makes `?` easier to use because its error type can accept any error, so you do not
/// need to manually convert error types.
///
/// ### `anyhow::bail!` - Return an error immediately
///
/// Use `bail!` to return an error with a formatted message:
///
/// ```ignore
/// if x != expected {
///     anyhow::bail!("expected {}, got {}", expected, x);
/// }
/// ```
///
/// ### `anyhow::format_err!` - Create an error without returning
///
/// Use `format_err!` when you need to create an error value without immediately returning:
///
/// ```ignore
/// let err = anyhow::format_err!("something went wrong: {}", details);
/// ```
///
/// ### `.context()` - Add context to errors
///
/// Use `.context()` to add helpful information when an error occurs. You must import the
/// trait first:
///
/// ```ignore
/// use anyhow::Context;
///
/// let file = std::fs::read("config.txt")
///     .context("failed to read config file")?;
/// ```
///
/// This wraps the underlying IO error with your message, producing output like:
/// "failed to read config file: No such file or directory"
pub(crate) type Result<T> = anyhow::Result<T>;

pub trait InteractiveProof {
    /// Input provided to both prover and verifier
    type Statement: Debug + Clone;
    /// Input provided to just verifier
    type Witness: Debug;

    /// Message sent by prover
    type ProverMessage: Clone + Debug + Send + 'static;
    /// Message sent by verifier
    type VerifierMessage: Clone + Debug + Send + 'static;

    /// What the prover outputs (assuming the protocol is successful)
    /// For all protocols except sumcheck, this will be () (i.e. prover outputs nothing)
    type ProverOutput: Debug;
    /// What the verifier outputs (assuming the protocol is successful)
    /// For all protocols except sumcheck, this will be () (i.e. prover outputs nothing)
    type VerifierOutput: Debug;

    /// The prover is represented by an 'asychronous' function that takes the statement, witness,
    /// and 'comms' which is the channel with which it can communicate with the verifier.
    async fn prover(
        stmt: Self::Statement,
        witness: Self::Witness,
        comms: Comms<Self::ProverMessage, Self::VerifierMessage>,
    ) -> Result<Self::ProverOutput>;

    /// The verifier is represented by an 'asychronous' function that takes the statement, witness,
    /// and 'comms' which is the channel with which it can communicate with the verifier.
    async fn verifier<R: Rng>(
        init: Self::Statement,
        comms: Comms<Self::VerifierMessage, Self::ProverMessage>,
        rng: &mut R,
    ) -> Result<Self::VerifierOutput>;
}

/// Execute protocol with the default thread-local RNG
/// These functions are largely for testing purposes. You should never actually have to run them
/// yourself.
pub async fn execute<P: InteractiveProof>(
    name: impl Into<String>,
    stmt: P::Statement,
    wit: P::Witness,
) -> (Result<P::ProverOutput>, Result<P::VerifierOutput>) {
    execute_with_rng::<P, _>(name, stmt, wit, &mut rand::rng()).await
}

/// Execute protocol with a provided RNG
/// These functions are largely for testing purposes. You should never actually have to run them
/// yourself.
pub async fn execute_with_rng<P: InteractiveProof, R: Rng>(
    name: impl Into<String>,
    stmt: P::Statement,
    wit: P::Witness,
    rng: &mut R,
) -> (Result<P::ProverOutput>, Result<P::VerifierOutput>) {
    let (prover_comms, verifier_comms) = Comms::pair(name);

    let mut prover = pin!(P::prover(stmt.clone(), wit, prover_comms));

    let mut verifier = pin!(P::verifier(stmt, verifier_comms, rng));

    tokio::select! {
        p = &mut prover => {
            if p.is_err() { (p, Err(anyhow::format_err!("prover exited early, aborting"))) }
            else { (p, verifier.await) }
        }
        v = &mut verifier => {
            if v.is_err() { (Err(anyhow::format_err!("verifier exited early, aborting")), v) }
            else { (prover.await, v) }
        }
    }
}
