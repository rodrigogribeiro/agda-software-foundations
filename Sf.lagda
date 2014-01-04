\documentclass{book}
\usepackage{a4}
\usepackage{palatino}
\usepackage{natbib}
\usepackage{amsmath,amsthm,proof}
\usepackage{amssymb}
\usepackage{amsfonts}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage{url}

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff


\newcommand{\M}[1]{\mathsf{#1}}
\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}

\newcommand{\us}[1]{\_\!#1\!\_}
\newtheorem{theorem}{Theorem}
\newtheorem{exe}{Exercise}[chapter]

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\F{" a "}"

%format -> = "\blue{\rightarrow}"

\newcommand{\nudge}[1]{\marginpar{\footnotesize #1}}

%format rewrite = "\mathkw{rewrite}"
%format constructor = "\mathkw{constructor}"
%format Set = "\D{Set}"
%format Ty = "\D{Ty}"
%format iota = "\C{\upiota}"
%format ->> = "\C{\rhd}"
%format _->>_ = "\_\!" ->> "\!\_"
%format * = "\C{\times}"
%format _*_ = "\_\!\," * "\,\!\_"
%format _==_ = "\_\!" == "\!\_"
%format Cx = "\D{Cx}"
%format QED = "\D{\Box}"
%format ++ = "\F{++}"
%format <> = "\D{nil}"
%format Em = "\C{\mathcal{E}}"
%format <: = "\D{\in}"
%format _<:_ = "\us{" <: "}"
%format Gam = "\V{\Gamma}"
%format Ren = "\F{Ren}"
%format Sub = "\F{Sub}"
%format Del = "\V{\Delta}"
%format sg = "\V{\sigma}"
%format tau = "\V{\tau}"
%format var = "\C{var}"
%format lam = "\C{lam}"
%format app = "\C{app}"
%format :: = "\!\raisebox{ -0.09in}[0in][0in]{\red{\textsf{`}}\,}"
%format _::_ = _ :: _
%format ? = "\orange{?}"
%format (HOLE (x) n) = { x } "\!_{" n "}"
%format GAP = "\;"

\begin{document}
  \title{Software Foundations}
  \maketitle
  \tableofcontents

%if False
\begin{code}
module Sf where
\end{code}
%endif

%include Preface.lagda
%include Basics.lagda
%include InductionProofs.lagda
%include Lists.lagda
%include Poly.lagda
%include MoreAgda.lagda
%include Propositions.lagda
%include MorePropositions.lagda
%include Logic.lagda
\end{document}
