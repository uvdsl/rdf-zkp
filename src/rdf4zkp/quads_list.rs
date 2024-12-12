use sophia::{
    api::{
        dataset::{CollectibleDataset, DQuadSource, MdResult},
        prelude::{Dataset, MutableDataset},
        quad::Gspo,
        source::{QuadSource, StreamResult},
        term::{
            matcher::{GraphNameMatcher, TermMatcher},
            GraphName, Term,
        },
    },
    inmem::index::{GraphNameIndex, TermIndex},
};

pub struct QuadsList<TI: TermIndex> {
    terms: TI,
    quads: Vec<[TI::Index; 4]>,
}

impl<TI: GraphNameIndex + Default> QuadsList<TI> {
    /// Construct an empty dataset
    pub fn new() -> Self {
        Self {
            terms: TI::default(),
            quads: Vec::new(),
        }
    }
}

impl<TI: GraphNameIndex + Default> CollectibleDataset for QuadsList<TI> {
    fn from_quad_source<QS: QuadSource>(
        mut quads: QS,
    ) -> StreamResult<Self, QS::Error, Self::Error> {
        let mut d = Self::new();
        quads.try_for_each_quad(|q| d.insert_quad(q).map(|_| ()))?;
        Ok(d)
    }
}

impl<TI: GraphNameIndex> MutableDataset for QuadsList<TI> {
    type MutationError = TI::Error;

    fn insert<TS, TP, TO, TG>(
        &mut self,
        s: TS,
        p: TP,
        o: TO,
        g: GraphName<TG>,
    ) -> MdResult<Self, bool>
    where
        TS: Term,
        TP: Term,
        TO: Term,
        TG: Term,
    {
        let is = self.terms.ensure_index(s)?;
        let ip = self.terms.ensure_index(p)?;
        let io = self.terms.ensure_index(o)?;
        let ig = match g {
            None => self.terms.get_default_graph_index(),
            Some(gn) => self.terms.ensure_index(gn)?,
        };
        self.quads.push([ig, is, ip, io]);
        Ok(true)
    }

    /// ! to be implemented if you want to use it...
    fn remove<TS, TP, TO, TG>(
        &mut self,
        s: TS,
        p: TP,
        o: TO,
        g: GraphName<TG>,
    ) -> MdResult<Self, bool>
    where
        TS: Term,
        TP: Term,
        TO: Term,
        TG: Term,
    {
        Ok(false)
    }
}

impl<TI: GraphNameIndex> Dataset for QuadsList<TI> {
    type Quad<'x> = Gspo<<TI::Term as Term>::BorrowTerm<'x>> where Self: 'x;
    type Error = TI::Error;

    fn quads(&self) -> DQuadSource<Self> {
        Box::new(self.quads.iter().map(|[gi, ti @ ..]| {
            Ok((
                self.terms.get_graph_name(*gi),
                ti.map(|i| self.terms.get_term(i)),
            ))
        }))
    }

    /// ! to be implemented if you want to use it...
    fn quads_matching<'s, S, P, O, G>(
        &'s self,
        sm: S,
        pm: P,
        om: O,
        gm: G,
    ) -> sophia::api::dataset::DQuadSource<'s, Self>
    where
        S: TermMatcher + 's,
        O: TermMatcher + 's,
        P: TermMatcher + 's,
        G: GraphNameMatcher + 's,
    {
        // Err("To be implemented");
        return Box::new(std::iter::empty());
    }
}
