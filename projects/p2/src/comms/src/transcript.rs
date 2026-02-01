use std::fmt;
use std::io::Write;
use std::sync::{Arc, Mutex};
use tracing::{Event, Subscriber, span};
use tracing_subscriber::{
    Layer,
    fmt::{FmtContext, FormatEvent, FormatFields, MakeWriter, format::Writer},
    layer::SubscriberExt,
    registry::LookupSpan,
};

#[derive(Default, Debug, Clone)]
struct SpanData {
    protocol: Option<String>,
    party: Option<String>,
    is_send: bool,
    is_recv: bool,
}

struct ProtocolLayer;

impl<S> Layer<S> for ProtocolLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(
        &self,
        attrs: &span::Attributes<'_>,
        id: &span::Id,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let span = ctx.span(id).unwrap();
        let mut data = SpanData::default();

        let name = attrs.metadata().name();
        data.is_send = name == "send";
        data.is_recv = name == "recv";

        let mut visitor = FieldVisitor::default();
        attrs.record(&mut visitor);
        data.protocol = visitor.protocol;
        data.party = visitor.party;

        span.extensions_mut().insert(data);
    }
}

#[derive(Default)]
struct FieldVisitor {
    protocol: Option<String>,
    party: Option<String>,
}

impl tracing::field::Visit for FieldVisitor {
    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        match field.name() {
            "protocol" => self.protocol = Some(value.to_string()),
            "party" => self.party = Some(value.to_string()),
            _ => {}
        }
    }

    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn fmt::Debug) {
        let target = match field.name() {
            "protocol" => &mut self.protocol,
            "party" => &mut self.party,
            _ => return,
        };
        *target = Some(format!("{value:?}").trim_matches('"').to_string());
    }
}

#[derive(Debug)]
struct ProtocolFormatter {
    show_send: bool,
    show_recv: bool,
    show_prover: bool,
    show_verifier: bool,
}

impl Default for ProtocolFormatter {
    fn default() -> Self {
        Self {
            show_send: true,
            show_recv: true,
            show_prover: true,
            show_verifier: true,
        }
    }
}

impl ProtocolFormatter {
    fn from_env() -> Self {
        let Ok(filter) = std::env::var("TRANSCRIPT_FILTER") else {
            return Self::default();
        };

        // Empty filter means show nothing
        if filter.is_empty() {
            return Self {
                show_send: false,
                show_recv: false,
                show_prover: false,
                show_verifier: false,
            };
        }

        let mut send = false;
        let mut recv = false;
        let mut prover = false;
        let mut verifier = false;

        for part in filter.split(',').map(str::trim) {
            match part {
                "send" => send = true,
                "recv" => recv = true,
                "prover" => prover = true,
                "verifier" => verifier = true,
                _ => {}
            }
        }

        let has_direction = send || recv;
        let has_party = prover || verifier;

        Self {
            show_send: !has_direction || send,
            show_recv: !has_direction || recv,
            show_prover: !has_party || prover,
            show_verifier: !has_party || verifier,
        }
    }

    fn should_show(&self, is_send: bool, is_recv: bool, party: Option<&str>) -> bool {
        let direction_ok = match (is_send, is_recv) {
            (true, _) => self.show_send,
            (_, true) => self.show_recv,
            _ => true,
        };

        let party_ok = match party {
            Some("prover") => self.show_prover,
            Some("verifier") => self.show_verifier,
            _ => true,
        };

        direction_ok && party_ok
    }
}

impl<S, N> FormatEvent<S, N> for ProtocolFormatter
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        mut writer: Writer<'_>,
        event: &Event<'_>,
    ) -> fmt::Result {
        let mut protocol = None;
        let mut party = None;
        let mut is_send = false;
        let mut is_recv = false;
        let mut depth = 0usize;

        if let Some(scope) = ctx.event_scope() {
            for span in scope {
                let exts = span.extensions();
                if let Some(data) = exts.get::<SpanData>() {
                    if data.protocol.is_some() {
                        depth += 1;
                    }
                    protocol = protocol.or_else(|| data.protocol.clone());
                    party = party.or_else(|| data.party.clone());
                    is_send |= data.is_send;
                    is_recv |= data.is_recv;
                }
            }
        }

        if !self.should_show(is_send, is_recv, party.as_deref()) {
            return Ok(());
        }

        let mut visitor = MessageVisitor::default();
        event.record(&mut visitor);

        if visitor.msg.is_empty() {
            return Ok(());
        }

        let arrow = match (is_send, is_recv) {
            (true, _) => "→",
            (_, true) => "←",
            _ => "?",
        };

        let party_display = match party.as_deref() {
            Some("prover") => "P",
            Some("verifier") => "V",
            _ => "?",
        };

        let indent = "  ".repeat(depth.saturating_sub(1));

        writeln!(
            writer,
            "{indent}{party_display} {arrow} [{}] {}",
            protocol.as_deref().unwrap_or_default(),
            visitor.msg
        )
    }
}

#[derive(Default)]
struct MessageVisitor {
    msg: String,
}

impl tracing::field::Visit for MessageVisitor {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn fmt::Debug) {
        if field.name() == "msg" {
            self.msg = format!("{value:?}").trim_matches('"').to_string();
        }
    }
}

#[derive(Clone)]
struct BufferedWriter(Arc<Mutex<Vec<u8>>>);

impl Write for BufferedWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl<'a> MakeWriter<'a> for BufferedWriter {
    type Writer = BufferedWriter;

    fn make_writer(&'a self) -> Self::Writer {
        self.clone()
    }
}

pub struct TranscriptGuard {
    _guard: tracing::subscriber::DefaultGuard,
    buffer: Arc<Mutex<Vec<u8>>>,
}

impl Drop for TranscriptGuard {
    fn drop(&mut self) {
        let buf = self.buffer.lock().unwrap();
        print!("{}", String::from_utf8_lossy(&buf));
    }
}

pub fn show_transcript() -> TranscriptGuard {
    let buffer = Arc::new(Mutex::new(Vec::new()));
    let writer = BufferedWriter(buffer.clone());

    let subscriber = tracing_subscriber::registry().with(ProtocolLayer).with(
        tracing_subscriber::fmt::layer()
            .event_format(ProtocolFormatter::from_env())
            .with_ansi(false)
            .with_writer(writer),
    );

    TranscriptGuard {
        _guard: tracing::subscriber::set_default(subscriber),
        buffer,
    }
}
