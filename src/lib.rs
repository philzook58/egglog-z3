use egg_smol::ast::{Expr, Literal};
use egg_smol::sort::*;
use egg_smol::util::IndexSet;
use egg_smol::PrimitiveLike;
use egg_smol::{EGraph, Value};
use std::any::Any;
use std::mem;
use std::sync::Arc;
use std::sync::Mutex;
pub use symbol_table::GlobalSymbol as Symbol;
type ArcSort = Arc<dyn Sort>;
/*

Z3Bool vs (Z3 bool) as sort. meh. Does it matter much?

I can specialize Z3Sort to Z3Bool, etc so long as I use the Arc<Context>
That is nice.

*/

// No. Z3Ast implements hash.
// So I can use a regular indexset.

/*
There are a couple choices:
1. Z3Sort<'ctx>. This was not working. There is something wrong about 'ctx which comes from the held Context anyhow.
2. Rebuild the high level z3 bindings from z3_sys to allow for hashmap storage of asts. This will largely be highly replaicetd from what the z3 crate already does
3. Use 'static to remove the lifetime parameter from z3::ast::Dynamic. mem::trasnmute will be needed at certain spots,
 because the context is not static
4. Actually have a static global Z3 context avaiable.
5. Don't use bindings at all. Construct ast/s-expressions and call smt solver via string interface


*/
#[derive(Eq, Hash, PartialEq, Debug, Clone)]
struct Z3Ast(z3::ast::Dynamic<'static>);
impl ToString for Z3Ast {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}
#[derive(Debug)]
pub struct Z3Sort {
    name: Symbol,
    ctx: Arc<z3::Context>,
    stringsort: Arc<StringSort>,
    asts: Mutex<IndexSet<Z3Ast>>,
}

unsafe impl Send for Z3Sort {}
unsafe impl Sync for Z3Sort {}

impl Z3Sort {
    pub fn new(name: Symbol, stringsort: Arc<StringSort>) -> Self {
        let cfg = z3::Config::new();
        Self {
            name,
            ctx: Arc::new(z3::Context::new(&cfg)),
            stringsort,
            asts: Default::default(),
        }
    }
}

struct Z3True {
    name: Symbol,
    sort: Arc<Z3Sort>,
}

impl PrimitiveLike for Z3True {
    fn name(&self) -> Symbol {
        self.name
    }

    fn accept(&self, types: &[ArcSort]) -> Option<ArcSort> {
        match types {
            [] => Some(self.sort.clone()),
            _ => None,
        }
    }

    fn apply(&self, values: &[Value]) -> Option<Value> {
        assert!(values.is_empty());
        let sort = self.sort.clone();
        let ctx: &z3::Context = &sort.ctx;
        let ctx: &'static z3::Context = unsafe { mem::transmute(ctx) };
        let d = Z3Ast(z3::ast::Dynamic::from(z3::ast::Bool::from_bool(ctx, true)));
        d.store(&sort)
    }
}

//example constant
struct Z3False {
    name: Symbol,
    sort: Arc<Z3Sort>,
}

impl PrimitiveLike for Z3False {
    fn name(&self) -> Symbol {
        self.name
    }

    fn accept(&self, types: &[ArcSort]) -> Option<ArcSort> {
        match types {
            [] => Some(self.sort.clone()),
            _ => None,
        }
    }

    fn apply(&self, values: &[Value]) -> Option<Value> {
        assert!(values.is_empty());
        let sort = self.sort.clone();
        let ctx: &z3::Context = &sort.ctx;
        let ctx: &'static z3::Context = unsafe { mem::transmute(ctx) };
        let d = Z3Ast(z3::ast::Bool::from_bool(ctx, false).into());
        d.store(&sort)
    }
}

// example unop
struct Z3Not {
    name: Symbol,
    sort: Arc<Z3Sort>,
}

impl PrimitiveLike for Z3Not {
    fn name(&self) -> Symbol {
        self.name
    }

    fn accept(&self, types: &[ArcSort]) -> Option<ArcSort> {
        match types {
            [t] => {
                if t.name() == "Z3Sort".into() {
                    Some(self.sort.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn apply(&self, values: &[Value]) -> Option<Value> {
        match values {
            [x] => {
                let sort = &self.sort;
                let d = Z3Ast::load(sort, x);
                let d = Z3Ast(d.0.as_bool().unwrap().not().into());
                d.store(sort)
            }
            _ => panic!("Z3-not called on wrong number of arguments"),
        }
    }
}

// example binop
struct Z3And {
    name: Symbol,
    sort: Arc<Z3Sort>,
}

impl PrimitiveLike for Z3And {
    fn name(&self) -> Symbol {
        self.name
    }

    fn accept(&self, types: &[ArcSort]) -> Option<ArcSort> {
        match types {
            [t, t2] => {
                if t.name() == "Z3Sort".into() && t2.name() == "Z3Sort".into() {
                    Some(self.sort.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn apply(&self, values: &[Value]) -> Option<Value> {
        match values {
            [x, y] => {
                let sort = &self.sort;
                let x = Z3Ast::load(sort, x).0.as_bool().unwrap();
                let y = Z3Ast::load(sort, y).0.as_bool().unwrap();
                let d = Z3Ast((x & y).into());
                d.store(sort)
            }
            _ => panic!("Z3-and called on wrong number of arguments"),
        }
    }
}

struct Z3Check {
    name: Symbol,
    sort: Arc<Z3Sort>,
}

impl PrimitiveLike for Z3Check {
    fn name(&self) -> Symbol {
        self.name
    }

    fn accept(&self, types: &[ArcSort]) -> Option<ArcSort> {
        match types {
            [t] => {
                if t.name() == "Z3Sort".into() {
                    Some(self.sort.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn apply(&self, values: &[Value]) -> Option<Value> {
        match values {
            [x] => {
                let sort = &self.sort;
                let x = Z3Ast::load(sort, x).0.as_bool().unwrap();
                let s = z3::Solver::new(&self.sort.ctx);
                s.assert(&x);
                let res = s.check();
                let res: &str = match res {
                    z3::SatResult::Sat => "\"sat\"",
                    z3::SatResult::Unsat => "\"unsat\"",
                    z3::SatResult::Unknown => "\"unknown\"",
                };
                let res: Symbol = res.into();
                res.store(&self.sort.stringsort)
            }
            _ => panic!("Z3-and called on wrong number of arguments"),
        }
    }
}

impl Sort for Z3Sort {
    fn name(&self) -> Symbol {
        self.name
    }

    fn as_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync + 'static> {
        self
    }

    fn register_primitives(self: Arc<Self>, egraph: &mut EGraph) {
        egraph.add_primitive(Z3True {
            name: "z3true".into(),
            sort: self.clone(),
        });
        egraph.add_primitive(Z3False {
            name: "z3false".into(),
            sort: self.clone(),
        });
        egraph.add_primitive(Z3Not {
            name: "not".into(),
            sort: self.clone(),
        });
        egraph.add_primitive(Z3And {
            name: "and".into(),
            sort: self.clone(),
        });
        egraph.add_primitive(Z3Check {
            name: "check-sat".into(),
            sort: self,
        });
    }

    fn make_expr(&self, value: Value) -> Expr {
        assert!(value.tag == self.name);
        let ast = Z3Ast::load(self, &value);
        Expr::Lit(Literal::String(ast.to_string().into()))
    }
}

impl IntoSort for Z3Ast {
    type Sort = Z3Sort;
    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort.asts.lock().unwrap().insert_full(self);
        Some(Value {
            tag: sort.name,
            bits: i as u64,
        })
    }
}

impl FromSort for Z3Ast {
    type Sort = Z3Sort;
    fn load(sort: &Self::Sort, value: &Value) -> Self {
        let i = value.bits as usize;
        (*sort.asts.lock().unwrap().get_index(i).unwrap()).clone()
    }
}
