use eframe::egui::{self, mutex::Mutex};
use std::{
    path::PathBuf,
    sync::{
        Arc,
        mpsc::{Receiver, Sender},
    },
    thread::JoinHandle,
};

use solar_magic::{
    cart::Cart, disasm::Disassembler, original_cart::OriginalCart, rewriter::Rewriter,
};

#[derive(Clone)]
enum LoaderMsg {
    FileOpen(Option<PathBuf>),
    NewCart(Arc<OriginalCart>),
    NewDisasm(Arc<Disassembler>),
    NewRewrite(Box<Rewriter>),
    IoError(Arc<std::io::Error>),
}

struct LoaderThread {
    handle: JoinHandle<()>,
    description: Arc<Mutex<Option<String>>>,
}

pub struct AppProject {
    send: Sender<LoaderMsg>,
    recv: Receiver<LoaderMsg>,
    threads: Vec<LoaderThread>,
    is_picker_open: bool,
    pub cart: Option<Arc<OriginalCart>>,
    pub disasm: Option<Arc<Disassembler>>,
    pub rewriter: Option<Box<Rewriter>>,
}

impl AppProject {
    pub fn new() -> Self {
        let (send, recv) = std::sync::mpsc::channel();
        Self {
            send,
            recv,
            threads: vec![],
            is_picker_open: false,
            cart: None,
            disasm: None,
            rewriter: None,
        }
    }

    pub fn get_description(&self) -> Option<String> {
        let items: Vec<String> = self
            .threads
            .iter()
            .filter_map(|t| t.description.lock().as_ref().cloned())
            .collect();
        if items.is_empty() {
            None
        } else {
            Some(items.join(", "))
        }
    }

    fn spawn_thread(
        &mut self,
        ctx: Option<&egui::Context>,
        f: impl FnOnce(&Sender<LoaderMsg>, &Mutex<Option<String>>) + Send + 'static,
    ) {
        let ctx = ctx.cloned();
        let send = self.send.clone();
        let description = Arc::new(Mutex::new(None));
        let desc = description.clone();
        let handle = std::thread::spawn(move || {
            f(&send, &desc);
            if let Some(ctx) = ctx {
                ctx.request_repaint();
            }
        });
        self.threads.push(LoaderThread {
            handle,
            description,
        })
    }

    pub fn update(&mut self, ctx: &egui::Context, mut on_err: impl FnMut(&std::io::Error)) {
        while let Ok(msg) = self.recv.try_recv() {
            match msg {
                LoaderMsg::FileOpen(path) => {
                    self.is_picker_open = false;
                    if let Some(path) = path {
                        self.load_cart(ctx, path);
                    }
                }
                LoaderMsg::NewCart(cart) => {
                    self.start_disasm(ctx, cart.clone());
                    self.cart = Some(cart);
                }
                LoaderMsg::NewDisasm(disasm) => {
                    self.disasm = Some(disasm);
                    self.start_rewrite(ctx);
                }
                LoaderMsg::NewRewrite(rewriter) => {
                    self.rewriter = Some(rewriter);
                }
                LoaderMsg::IoError(err) => on_err(&err),
            }
        }
        self.threads
            .extract_if(.., |thread| thread.handle.is_finished())
            .filter_map(|thread| thread.handle.join().err())
            .for_each(|_err| {
                on_err(&std::io::Error::other("loader thread died"));
            });
    }

    pub fn load_cart(&mut self, ctx: &egui::Context, path: PathBuf) {
        fn load_cart(path: PathBuf) -> std::io::Result<OriginalCart> {
            let bytes = std::fs::read(path)?;
            let cart = Cart::from_bytes(bytes);
            OriginalCart::new(cart)
                .map_err(|_| std::io::Error::other("not an original Super Mario World cart"))
        }
        self.spawn_thread(Some(ctx), |sender, desc| {
            *desc.lock() = Some("Loading cartridge".to_string());
            let res = load_cart(path);
            let _err = match res {
                Ok(cart) => sender.send(LoaderMsg::NewCart(Arc::new(cart))),
                Err(err) => sender.send(LoaderMsg::IoError(Arc::new(err))),
            };
        });
    }

    pub fn start_disasm(&mut self, ctx: &egui::Context, cart: Arc<OriginalCart>) {
        self.spawn_thread(Some(ctx), move |sender, desc| {
            *desc.lock() = Some("Disassemble cartridge binary".to_string());
            let mut disasm = solar_magic::disasm::Disassembler::new();
            disasm.add_vectors(&cart.cart);
            disasm.disassemble(&cart.cart);
            let _err = sender.send(LoaderMsg::NewDisasm(Arc::new(disasm)));
        });
    }

    pub fn start_rewrite(&mut self, ctx: &egui::Context) {
        let (Some(cart), Some(disasm)) =
            (self.cart.as_ref().cloned(), self.disasm.as_ref().cloned())
        else {
            return;
        };
        self.spawn_thread(Some(ctx), move |sender, desc| {
            *desc.lock() = Some("Static rewrite cartridge disassembly".to_string());
            let mut rewriter = solar_magic::rewriter::Rewriter::new();
            rewriter.rewrite(&cart.cart, &disasm);
            let _err = sender.send(LoaderMsg::NewRewrite(Box::new(rewriter)));
        });
    }

    pub fn start_file_picker(&mut self) {
        if self.is_picker_open {
            return;
        }
        self.is_picker_open = true;
        self.spawn_thread(None, move |sender, _| {
            let _err = sender.send(LoaderMsg::FileOpen(rfd::FileDialog::new().pick_file()));
        });
    }
}
