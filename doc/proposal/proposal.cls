\ProvidesClass{proposal}[2021/02/26]
\NeedsTeXFormat{LaTeX2e}

\LoadClassWithOptions{scrartcl}
\KOMAoptions{paper=a4,DIV=12}

\RequirePackage{lmodern}
\RequirePackage[T1]{fontenc}
\RequirePackage{paralist}
\RequirePackage{natbib}
\RequirePackage[usenames,dvipsnames]{xcolor}
\RequirePackage{ETHlogo}
\RequirePackage{etoolbox}

\renewcommand{\familydefault}{\sfdefault}

\newcommand{\proposal@title}{Title of Proposal}
\renewcommand{\title}[1]{\renewcommand{\proposal@title}{#1}}

\newcommand{\proposal@type}{Type of Proposal}
\newcommand{\type}[1]{\renewcommand{\proposal@type}{#1}}

\newcommand{\proposal@supervisorlbl}{Supervisor}
\newcommand{\proposal@supervisor}{supervisor}
\newcommand{\proposalsupervisor}[2][Supervisor]{
  \renewcommand{\proposal@supervisorlbl}{#1}%
  \renewcommand{\proposal@supervisor}{#2}%
}

\newcommand{\proposal@issuedate}{issue date}
\newcommand{\proposalissuedate}[1]{\renewcommand{\proposal@issuedate}{#1}}

\renewcommand{\maketitle}{%
  \begin{minipage}{\textwidth}
    \ETHlogo[60mm]
  \end{minipage}
  \par
  \begin{center}
    {\rule{\textwidth}{.5pt}}
  \end{center}
  \begin{center}
    {\Large \proposal@type}\\
    \medskip
    {\huge \textbf{\proposal@title}\\}
    \bigskip
    \begin{tabular}{@{}ll@{}}
      {\proposal@supervisorlbl}: & {\proposal@supervisor} \\
      Professor:   & Prof.\ David Basin \\
      Issue date:  & {\proposal@issuedate} \\
    \end{tabular}
  \end{center}
  \begin{center}
    {\rule{\textwidth}{.5pt}}
  \end{center}
}

\AtBeginDocument{\maketitle}

\setcounter{secnumdepth}{0}
\RedeclareSectionCommand[
%afterindent=false,
  beforeskip=\baselineskip,
  afterskip=0.5\baselineskip
]{section}

\BeforeBeginEnvironment{document}{
  \RequirePackage{hyperref}
  \hypersetup{
    colorlinks=true,
    citecolor=MidnightBlue,
    urlcolor=OliveGreen,
    anchorcolor=Red
  }
}
