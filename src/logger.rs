use std::cell::RefCell;
use std::rc::Rc;

pub struct LogEntry {
    pub info: String,
    pub phrase: String,
    pub details: Rc<RefCell<Logger>>,
}

impl LogEntry {
    pub fn new(info: String, phrase: String) -> Self {
        Self {
            info,
            phrase,
            details: Logger::new(),
        }
    }
}

pub struct Logger {
    pub entries: Vec<LogEntry>,
}

impl Logger {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            entries: Vec::new(),
        }))
    }

    pub fn log(&mut self, info: String, phrase: String) -> &mut Logger {
        let entry = LogEntry::new(info, phrase);
        self.entries.push(entry);
        self
    }

    pub fn new_entry(&mut self, info: String, phrase: String) -> &mut LogEntry {
        let entry = LogEntry::new(info, phrase);
        self.entries.push(entry);
        self.entries.last_mut().unwrap()
    }

    pub fn sublog(&mut self, info: String, phrase: String) -> Rc<RefCell<Logger>> {
        self.new_entry(info, phrase).details.clone()
    }
}
