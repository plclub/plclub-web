<?php 
      $this_page = "results"; 
      $version = '$Id: results.php,v 1.4 2004/09/30 18:53:27 jnfoster Exp $';
      include("header.php") 
?>

We are happy to announce the results of the 2004 ICFP Programming Contest:
<ul>
  <li><a href="#judges">Judge's Prize</a> </li>
  <li><a href="#lightning">Winner, Lightning Division</a> </li>
  <li><a href="#second">Second Place, Main Division</a> </li>
  <li><a href="#first">First Place, Main Division</a> </li>
  <li><a href="#tourney">Tournament Structure</a> </li>
  <li><a href="#standings-lightning">Full Lightning Division Results</a> </li>
  <li><a href="#standings-main">Full Main Division Results</a> </li>
  <li><a href="#languages">Language Statistics</a> </li>
</ul>

<p>
<table>
<tr><td class="red"><b><a name="judges">Judge's Prize</a></b></td></tr>
<tr><td>
This year, the judge's prize is awarded to the team with the coolest ant
meta-language.
</td></tr>
<tr><td>
Team name: <a href="http://cristal.inria.fr/~regisgia/icfp04.shtml">Team OCant</a>
<p>
Webpage: <a href="http://cristal.inria.fr/~regisgia/icfp04.shtml">http://cristal.inria.fr/~regisgia/icfp04.shtml</a>
<p>
Members:
<table>
<tr><td>Damien Doligez</td><td><tt>damien.doligez@inria.fr</tt></td>
<tr><td>Thomas Dufour</td><td><tt>Thomas.Dufour@ens.fr</tt></td>
<tr><td>Stephane Gimenez</td><td><tt>Stephane.Gimenez@ens-lyon.fr</tt></td>
<tr><td>David Haguenauer</td><td><tt>David.Haguenauer@inria.fr</tt></td>
<tr><td>Gregoire Henry</td><td><tt>Gregoire.Henry@etu.upmc.fr</tt></td>
<tr><td>Xavier Leroy</td><td><tt>xavier.leroy@inria.fr</tt></td>
<tr><td>Yann Regis-Gianas</td><td><tt>Yann.Regis-Gianas@inria.fr</tt></td>
<tr><td>Pierre-Yves Strub</td><td><tt>strub@macs.hw.ac.uk</tt></td>
<tr><td>Samuel Thibault</td><td><tt>samuel.thibault@ens-lyon.fr</tt></td>
<tr><td>Boris Yakobowski</td><td><tt>Boris.Yakobowski@inria.fr</tt></td>
</table>
<p>
Meta-languages: OCaml
<p>
Ant language (from the README): We use a high-level language to
program our ants (with, but not limited to, "try with" statements,
conditionals, loops, function calls (with parameters), higher-order,
error reporting...). Xavier Leroy provided us with a compiler that
takes AML (Ant Meta Language) and produces ant brain code. The
compiler was extended to handle (possibly mutual) recursion for
non-returning functions.  It also provides removal of dead states, and
compaction of bi-simulable states. The AML compiler is, of course,
written in Objective Caml.
<p>
Strategy:
<ul>
  <li>Ants differentiate at the beginning into Explorers, Wanderers, and Guards.</li>
  <li>Explorers build radial trails, alternating 0, 1, and 2 marks.  They
     are pretty smart about dodging rocks without getting confused about
     directions.  When they get stuck or find the foe anthill, they
     start wandering.</li>
  <li>When a wanderer or an explorer finds food, it follows the trail
     back home, laying down a parallel trail of 3 marks as they go.
     This enables other ants to find the food by walking along the 0/1/2
     trails and sensing to the side for 3 marks.</li>
  <li>When a food cache runs out, an Eraser ant takes away the 3 marks.</li>
  <li>Guards stay at home and form a safe pattern (a length 6 circle) in
     the anthill.</li>
</ul>
<p>
The judges declare: 
<br><br>
<h3 class="green">"Team OCant are an extremely cool bunch of hackers!"</h3>
<br><br>
</tr></td>

<tr><td class="red"><b>Lightning Division</b></td></tr>
<tr><td>
Lighning entries were submitted within 24 hours. This year 52 teams entered the lightning division.
</td></tr>

<tr><td class="red"><b><a name="lightning">Winner, Lightning Division</a></b></td></tr>
<tr><td>
Team Name: <a href="http://rad-eye.com/icfp2004/">The RedTeam</a>
<p>
Webpage: <a href="http://rad-eye.com/icfp2004/">http://rad-eye.com/icfp2004</a>
<p>
Members:
<table>
<tr><td>John Dethridge</td><td><tt>johndethridge@gmail.com</tt></td></tr>
<tr><td>Lars Backstrom</td><td><tt>lb87@cornell.edu</tt></td></tr>
<tr><td>Jon Macalister</td><td></td></tr>
<tr><td>Stefan Pochmann</td><td></td></tr>
<tr><td>Josef Rokicki</td><td></td></tr>
<tr><td>Tom Rokicki</td><td><tt>rokicki@cs.stanford.edu</tt></td></tr>
<tr><td>Daniel Wright</td><td><tt>dmwright@cs.stanford.edu</tt></td></tr>
</table>
Meta-languages: Java, C++, Perl, and m4.
<p>
Ant language:
<br>
"Allows macros, if and while constructions, and labels."
<p>
Strategies:
<ul>
<li>leaving directed trails from home to quickly find way back (lightning)</li>
<li>squating on food in home base to protect from stealing     (lightning)</li>
<li>attacking home base traps to protect collected food</li>
<li>double action expeditionary traps</li>
<li>foe home surround</li>
</ul>
<p>
Comments:
<br>
The ultimate goal of the contest is to collect as much food as
fast as possible. But this is no fun. Attacking and killing other
ants is, and the Red Team is the foremost innovator of various
attack strategies!
<ul>
<li>One attack strategy involves a seemingly mis-placed formation
   of five ants next to a food pile at home. When a clueless ant
   rushes to steal some "unprotected" food, the formation swiftly
   shifts one step consuming the intruder and adding three free
   food pieces to its pile. (See video.)
   <p>
   Incidently, when some ants from the five formation are blocked
   by enemy ants (for instance trying to surround the hill), the
   remaining ants maniacly snap back and forth unsuccessfully
   wasting a lot of calories. (See video.)</li>

<li>Another strategy involves five traveling ants setting up a
   two-sided trap close to the enemy anthill. When an opposing
   ant wanders in from the left or from the right, the top two
   ants and the bottom two ants slide in the appropriate
   direction annihilating the lost and unexpecting enemy. (See
   video.)</li>

<li>If not setting up traps outside the enemy hill, travelling
   ants may attempt to surround it. Once the anthill is fully
   surrounded, the opposing ants have no way of adding to its
   food supply or penetrating the surrounding chain since it is
   impossible to kill any of the surrounding ants. (See video.)</li>
</ul>
The lightning entry did not use most of these strategies. It
employed alternating three different combinations of markers to
create directed trails. The ants made thin trails away from the
base, and then once an ant found food, it could use these trails
to quickly get home. At home 'squatters' sit on our food in our
base in order to protect it from being stolen.
<p>
The judges hastily declare:
<br><br>
<h3 class="green">"Java and C++ are very suitable for rapid prototyping."</h3>
<br><br>
</td></tr>

<tr><td class="red"><b>Main Division</b></td></tr>
<tr><td>
Entries to the main division were submitted after 72 hours. This year there were 230 teams.
</td></tr>
<tr><td class="red"><b><a name="second">Second Place, Main Division</a></b></td></tr>
<tr><td>
Second Place Team: <a href="http://www.sawicki.us/icfp/2004">The Frictionless Bananas</a>
<p>
Webpage: <a href="http://www.sawicki.us/icfp/2004">http://www.sawicki.us/icfp/2004/</a>
<p>
Members: Jeremy Sawicki and Mieszko Lis
<p>

This team's submission consisted of a simulator and visualization tool
written in C++ that repeatedly outputs a textual representation of the
world.
<p>
To simplify the process of creating ants this team also developed a
Haskell macro-assembler for an enhanced form of ant assembly language.
Firstly, they added symbolic labels that could be referenced rather
than having to directly refer to machine states.  Secondly their
assembler encodes into the resulting state machine four bits of
information: which direction the ant is presently facing and whether
the ant is carrying food.  This information can then be used to
parameterize instructions.
<p>
Key features of their winning ant
<ul>
<li>Leave a trail indicating the direction ant is traveling.</li>
<li>Leave a trail upon returning from food.</li>
<li>Erase trails to exhausted food sources.</li>
<li>Guarding food on the ant-hill.</li>
<li>Local stockpiling of food rather than directly returning to the
ant-hill.</li>
</ul>
Prize: 
<p>
The judges declare:
<br><br>
<h2 class="green">"Haskell and C++ are fine programming tools for many applications."</h2>
<br><br>
</td></tr>

<tr><td class="red"><b><a name="first">First Place, Main Division</a></b></td></tr>
<tr><td>
Team Name: <a href="http://urchin.earth.li/icfpcontest/2004/">Dunkosmiloolump</a>
<p>
Webpage: <a href="http://urchin.earth.li/icfpcontest/2004/">http://urchin.earth.li/icfpcontest/2004</a>
<p>
Members:
<table>
<tr><td>Ian Lynagh</td><td><tt>igloo@earth.li</tt></tr></td>
<tr><td>Ganesh Sittampalam</td><td><tt>ganesh@earth.li</tt></tr></td>
<tr><td>Andres Loeh</td><td><tt>ksicfp@andres.loeh.de</tt></tr></td>
<tr><td>Duncan Coutts</td><td><tt>duncan.coutts@worcester.oxford.ac.uk</tt></tr></td>
</table>
<p>
Meta-Language: (from their README) Everything written in Haskell
(including the version control system - darcs); Consists of a compiler
for a (hurriedly designed!) combinator language, a simulator and a
visualizer.
<p>
Ant Language:
<ul>
<li>Has gotos and labels.</li>  
<li>Implemented as Haskell combinators, which are
   monadic for fresh label generation.</li>  
<li>Compiles to the low-level with
  optimizations: (1) inlines all gotos, (2) eliminates "common
  subexpressions" (i.e., shares common continuations) by introducing
  new gotos, (3) eliminates useless branches to identical states, (4)
  repeats all of these, and (5) replaces labels with state numbers.</li>
</ul>
<p>
Ant strategies:
<ul>
<li>Hill initialization is very clever (and complex), exploiting the
   "left to right, top to bottom" order of ant activation.  This
   enables twice as fast startup as it could be otherwise.</li>

<li>Food is gathered in one place in the hill and protected by 7 ants.
   Ants dropping food flow in one direction: they enter from southeast
   and exit to northwest.  This enables smooth traffic.</li>

<li>Ants leave trails to home (3 bits) and to food (the other 3 bits).
   The encoding (6 directions into 3 bits) is clever and enables them
   to omit some sensing (and perhaps marking).</li>

<li>Ants erase food trails if food source has exhausted.</li>

<li>Certain parameters (e.g., in random walking to find food) seem to
   be tuned by semi-automatic self-tournaments.</li>
</ul>
<p>
The judges declare;
<br><br>
<h1 class="green">"Haskell is the language of choice for discriminating
hackers!"</h1>
<br><br>
</td><tr>

<tr><td class="red"><b><a name="tourney">Tournament Structure</a></b></td></tr>
<tr><td>
Every qualified species of ants is matched against one another (other
than itself) _twice_, once as black and once as red, in each of 100
randomly generated worlds.  This solves the bias that a world may have
toward whichever one of the two colors.  2 points are given for a win
(i.e., having more food dropped on their hill than on the other hill
after 100,000 rounds) and 1 for a tie.  Each species is ranked
according to its total points.
<p>
There were 87 qualified ant species for the lightning division and 361
for the main division.  So the number of matches were
<p>
  87 * 86 * 100  =  748,200
<p>
and
<p>
  361 * 360 * 100  =  12,996,000
<p>
respectively.  Since they were executed in a 256-CPU cluster and each
match took several seconds, the whole tournaments took a few days
(excluding the time for debugging tcsh scripts).
<p>
  748,200 * 5 / 256 / 60 / 60 / 24  ~=  0.17
<p>
  12,996,000 * 5 / 256 / 60 / 60 / 24  ~=  2.94
<p>
</tr></td>

<tr><td class="red"><b><a name="standings-lightning">Full Lightning Division Results</a></b></td></tr>
<tr><td>
<center>
<table>
<tr><th>Place</th> <th>Points</th> <th>Team</th> <th>Team size</th> <th>Ant</th> <th>Approach</th> <th>Language</th> <th>Ant size</th></tr>
<tr><th align='right'>1</th><td align='right'>32868</td><td>RedTeam</td><td align='center'>7</td><td>L2</td><td>higher</td><td>Perl</td><td align='right'>1263</td></tr>
<tr><th align='right'>2</th><td align='right'>32811</td><td>RedTeam</td><td align='center'>7</td><td>L1</td><td>higher</td><td>Perl</td><td align='right'>1079</td></tr>
<tr><th align='right'>3</th><td align='right'>32230</td><td>MiMtim</td><td align='center'>4</td><td>L1</td><td>pre</td><td>OCaml</td><td align='right'>87</td></tr>
<tr><th align='right'>4</th><td align='right'>31422</td><td>MiMtim</td><td align='center'>4</td><td>L2</td><td>pre</td><td>OCaml</td><td align='right'>105</td></tr>
<tr><th align='right'>5</th><td align='right'>31322</td><td>kuma-</td><td align='center'>3</td><td>L1</td><td>pre</td><td>Ruby</td><td align='right'>650</td></tr>
<tr><th align='right'>6</th><td align='right'>31313</td><td>TAPLAS-tiny</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Perl</td><td align='right'>296</td></tr>
<tr><th align='right'>7</th><td align='right'>31255</td><td>TAPLAS-tiny</td><td align='center'>1</td><td>L2</td><td>pre</td><td>Perl</td><td align='right'>337</td></tr>
<tr><th align='right'>8</th><td align='right'>30863</td><td>Up Too Late</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Scheme</td><td align='right'>156</td></tr>
<tr><th align='right'>9</th><td align='right'>30546</td><td>kuma-</td><td align='center'>3</td><td>L2</td><td>pre</td><td>Ruby</td><td align='right'>656</td></tr>
<tr><th align='right'>10</th><td align='right'>30222</td><td>Busman Holiday Club</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Lisp</td><td align='right'>114</td></tr>
<tr><th align='right'>11</th><td align='right'>30204</td><td>Three-headed monkey </td><td align='center'>4</td><td>L2</td><td>pre</td><td>C++</td><td align='right'>142</td></tr>
<tr><th align='right'>12</th><td align='right'>30063</td><td>Three-headed monkey </td><td align='center'>4</td><td>L1</td><td>pre</td><td>C++</td><td align='right'>100</td></tr>
<tr><th align='right'>13</th><td align='right'>29959</td><td>Exo-plugarite Zulang</td><td align='center'>4</td><td>L1</td><td>pre</td><td>SML</td><td align='right'>1237</td></tr>
<tr><th align='right'>14</th><td align='right'>29825</td><td>Siegers</td><td align='center'>2</td><td>L1</td><td>higher</td><td>C</td><td align='right'>114</td></tr>
<tr><th align='right'>15</th><td align='right'>29025</td><td>Antsier</td><td align='center'>3</td><td>L1</td><td>higher</td><td>C</td><td align='right'>150</td></tr>
<tr><th align='right'>16</th><td align='right'>28817</td><td>Antsier</td><td align='center'>3</td><td>L2</td><td>higher</td><td>C</td><td align='right'>144</td></tr>
<tr><th align='right'>17</th><td align='right'>28799</td><td>Team OaSys</td><td align='center'>4</td><td>L1</td><td>higher</td><td>Perl</td><td align='right'>138</td></tr>
<tr><th align='right'>18</th><td align='right'>27597</td><td>GUIGNOL</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Python</td><td align='right'>86</td></tr>
<tr><th align='right'>19</th><td align='right'>25644</td><td>jabber.ru</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Tcl</td><td align='right'>27</td></tr>
<tr><th align='right'>20</th><td align='right'>24943</td><td>K.I.S.S.</td><td align='center'>2</td><td>L1</td><td>pre</td><td>Python</td><td align='right'>19</td></tr>
<tr><th align='right'>21</th><td align='right'>24912</td><td>Team Lone Haskeller</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Haskell</td><td align='right'>195</td></tr>
<tr><th align='right'>22</th><td align='right'>24406</td><td>Death by Duxx</td><td align='center'>3</td><td>L1</td><td>higher</td><td>Python</td><td align='right'>23</td></tr>
<tr><th align='right'>23</th><td align='right'>24402</td><td>Team Lone Haskeller</td><td align='center'>1</td><td>L2</td><td>pre</td><td>Haskell</td><td align='right'>192</td></tr>
<tr><th align='right'>24</th><td align='right'>24353</td><td>Tycon Mismatch</td><td align='center'>6</td><td>L1</td><td>higher</td><td>SML</td><td align='right'>21</td></tr>
<tr><th align='right'>25</th><td align='right'>24154</td><td>DylAntz</td><td align='center'>1</td><td>L2</td><td>higher</td><td>Perl</td><td align='right'>31</td></tr>
<tr><th align='right'>26</th><td align='right'>23893</td><td>Black Ice</td><td align='center'>1</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>18</td></tr>
<tr><th align='right'>27</th><td align='right'>23874</td><td>Black Ice</td><td align='center'>1</td><td>L2</td><td>hand</td><td>hand</td><td align='right'>18</td></tr>
<tr><th align='right'>28</th><td align='right'>23320</td><td>Tycon Mismatch</td><td align='center'>6</td><td>L2</td><td>higher</td><td>SML</td><td align='right'>88</td></tr>
<tr><th align='right'>29</th><td align='right'>23148</td><td>DylAntz</td><td align='center'>1</td><td>L1</td><td>higher</td><td>Perl</td><td align='right'>90</td></tr>
<tr><th align='right'>30</th><td align='right'>22858</td><td>Les Lampions</td><td align='center'>6</td><td>L1</td><td>unkn</td><td>unknown</td><td align='right'>160</td></tr>
<tr><th align='right'>31</th><td align='right'>22690</td><td>dCoy</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Java</td><td align='right'>17</td></tr>
<tr><th align='right'>32</th><td align='right'>22679</td><td>Sealab 2021</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Python</td><td align='right'>86</td></tr>
<tr><th align='right'>33</th><td align='right'>22299</td><td>KaNT</td><td align='center'>4</td><td>L1</td><td>higher</td><td>Java</td><td align='right'>100</td></tr>
<tr><th align='right'>34</th><td align='right'>21349</td><td>Captain Bluebear</td><td align='center'>1</td><td>L1</td><td>pre</td><td>OCaml</td><td align='right'>54</td></tr>
<tr><th align='right'>35</th><td align='right'>21191</td><td>shinichiro.h</td><td align='center'>1</td><td>L1</td><td>pre</td><td>D</td><td align='right'>1053</td></tr>
<tr><th align='right'>36</th><td align='right'>20994</td><td>KaNT</td><td align='center'>4</td><td>L2</td><td>higher</td><td>Java</td><td align='right'>500</td></tr>
<tr><th align='right'>37</th><td align='right'>18308</td><td>The Stansifer Family</td><td align='center'>3</td><td>L1</td><td>higher</td><td>Java</td><td align='right'>567</td></tr>
<tr><th align='right'>38</th><td align='right'>18240</td><td>ANTagoniste</td><td align='center'>2</td><td>L1</td><td>higher</td><td>C</td><td align='right'>14</td></tr>
<tr><th align='right'>39</th><td align='right'>17603</td><td>DDT</td><td align='center'>3</td><td>L1</td><td>pre</td><td>Haskell</td><td align='right'>3956</td></tr>
<tr><th align='right'>40</th><td align='right'>17327</td><td>DDT</td><td align='center'>3</td><td>L2</td><td>pre</td><td>Haskell</td><td align='right'>3956</td></tr>
<tr><th align='right'>41</th><td align='right'>17217</td><td>OneManWeekendFun</td><td align='center'>1</td><td>L1</td><td>pre</td><td>C++</td><td align='right'>38</td></tr>
<tr><th align='right'>42</th><td align='right'>17042</td><td>4060TEAM</td><td align='center'>3</td><td>L2</td><td>higher</td><td>Python</td><td align='right'>50</td></tr>
<tr><th align='right'>43</th><td align='right'>16581</td><td>Merion</td><td align='center'>1</td><td>L1</td><td>pre</td><td>OCaml</td><td align='right'>36</td></tr>
<tr><th align='right'>44</th><td align='right'>16228</td><td>4060TEAM</td><td align='center'>3</td><td>L1</td><td>higher</td><td>Python</td><td align='right'>37</td></tr>
<tr><th align='right'>45</th><td align='right'>16004</td><td>uguu.org</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Perl</td><td align='right'>129</td></tr>
<tr><th align='right'>46</th><td align='right'>15750</td><td>Merion</td><td align='center'>1</td><td>L2</td><td>pre</td><td>OCaml</td><td align='right'>29</td></tr>
<tr><th align='right'>47</th><td align='right'>15153</td><td>Ants Of Prey</td><td align='center'>5</td><td>L1</td><td>higher</td><td>m4</td><td align='right'>90</td></tr>
<tr><th align='right'>48</th><td align='right'>14926</td><td>SynthAnt</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Scheme</td><td align='right'>53</td></tr>
<tr><th align='right'>49</th><td align='right'>14541</td><td>SynthAnt</td><td align='center'>1</td><td>L2</td><td>pre</td><td>Scheme</td><td align='right'>68</td></tr>
<tr><th align='right'>50</th><td align='right'>14536</td><td>OYATU-kit-SOS!</td><td align='center'>11</td><td>L2</td><td>higher</td><td>Java</td><td align='right'>76</td></tr>
<tr><th align='right'>51</th><td align='right'>14429</td><td>Linepithema humile</td><td align='center'>2</td><td>L1</td><td>pre</td><td>OCaml</td><td align='right'>240</td></tr>
<tr><th align='right'>52</th><td align='right'>14298</td><td>OYATU-kit-SOS!</td><td align='center'>11</td><td>L1</td><td>higher</td><td>Java</td><td align='right'>35</td></tr>
<tr><th align='right'>53</th><td align='right'>14150</td><td>OneManWeekendFun</td><td align='center'>1</td><td>L2</td><td>pre</td><td>C++</td><td align='right'>17</td></tr>
<tr><th align='right'>54</th><td align='right'>13911</td><td>Packi</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Pascal</td><td align='right'>75</td></tr>
<tr><th align='right'>55</th><td align='right'>13201</td><td>NiceAnts</td><td align='center'>4</td><td>L1</td><td>unkn</td><td>unknown</td><td align='right'>41</td></tr>
<tr><th align='right'>56</th><td align='right'>12933</td><td>Les Lampions</td><td align='center'>6</td><td>L2</td><td>unkn</td><td>unknown</td><td align='right'>20</td></tr>
<tr><th align='right'>57</th><td align='right'>12910</td><td>Scott Family</td><td align='center'>2</td><td>L1</td><td>pre</td><td>Revolution</td><td align='right'>35</td></tr>
<tr><th align='right'>58</th><td align='right'>12883</td><td>Scott Family</td><td align='center'>2</td><td>L2</td><td>pre</td><td>Revolution</td><td align='right'>33</td></tr>
<tr><th align='right'>59</th><td align='right'>12723</td><td>random boke</td><td align='center'>1</td><td>L1</td><td>pre</td><td>C</td><td align='right'>25</td></tr>
<tr><th align='right'>60</th><td align='right'>11501</td><td>Detlef Pleiss</td><td align='center'>1</td><td>L2</td><td>mut</td><td>Java</td><td align='right'>17</td></tr>
<tr><th align='right'>61</th><td align='right'>11323</td><td>NiceTry</td><td align='center'>2</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>27</td></tr>
<tr><th align='right'>62</th><td align='right'>11117</td><td>Detlef Pleiss</td><td align='center'>1</td><td>L1</td><td>mut</td><td>Java</td><td align='right'>17</td></tr>
<tr><th align='right'>63</th><td align='right'>10948</td><td>JJK</td><td align='center'>1</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>37</td></tr>
<tr><th align='right'>64</th><td align='right'>10465</td><td>The Nemerlies</td><td align='center'>6</td><td>L1</td><td>higher</td><td>Nemerle</td><td align='right'>26</td></tr>
<tr><th align='right'>65</th><td align='right'>10051</td><td>The Green Onions</td><td align='center'>1</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>403</td></tr>
<tr><th align='right'>66</th><td align='right'>8481</td><td>fhqwhgads</td><td align='center'>1</td><td>L1</td><td>pre</td><td>Java</td><td align='right'>22</td></tr>
<tr><th align='right'>67</th><td align='right'>8463</td><td>fhqwhgads</td><td align='center'>1</td><td>L2</td><td>pre</td><td>Java</td><td align='right'>24</td></tr>
<tr><th align='right'>68</th><td align='right'>7809</td><td>The Nemerlies</td><td align='center'>6</td><td>L2</td><td>higher</td><td>Nemerle</td><td align='right'>216</td></tr>
<tr><th align='right'>69</th><td align='right'>7302</td><td>random boke</td><td align='center'>1</td><td>L2</td><td>pre</td><td>C</td><td align='right'>10000</td></tr>
<tr><th align='right'>70</th><td align='right'>7102</td><td>Prologin</td><td align='center'>2</td><td>L1</td><td>higher</td><td>C++</td><td align='right'>217</td></tr>
<tr><th align='right'>71</th><td align='right'>6633</td><td>Team PacSoft</td><td align='center'>6</td><td>L1</td><td></td><td>Haskell</td><td align='right'>29</td></tr>
<tr><th align='right'>72</th><td align='right'>6598</td><td>Team OaSys</td><td align='center'>4</td><td>L2</td><td>higher</td><td>Perl</td><td align='right'>9</td></tr>
<tr><th align='right'>73</th><td align='right'>5916</td><td>Andrey Stolyarov</td><td align='center'>1</td><td>L1</td><td>pre</td><td>C++</td><td align='right'>125</td></tr>
<tr><th align='right'>74</th><td align='right'>5809</td><td>Andrey Stolyarov</td><td align='center'>1</td><td>L2</td><td>pre</td><td>C++</td><td align='right'>125</td></tr>
<tr><th align='right'>75</th><td align='right'>5514</td><td>Hollandians</td><td align='center'>2</td><td>L1</td><td>mut</td><td>C</td><td align='right'>1167</td></tr>
<tr><th align='right'>76</th><td align='right'>5481</td><td>Hollandians</td><td align='center'>2</td><td>L2</td><td>mut</td><td>C</td><td align='right'>8400</td></tr>
<tr><th align='right'>77</th><td align='right'>3604</td><td>Ants Of Prey</td><td align='center'>5</td><td>L2</td><td>higher</td><td>m4</td><td align='right'>2</td></tr>
<tr><th align='right'>78</th><td align='right'>3494</td><td>FormiX (formerly LIX</td><td align='center'>3</td><td>L1</td><td>pre</td><td>OCaml</td><td align='right'>756</td></tr>
<tr><th align='right'>79</th><td align='right'>3430</td><td>Virdemar</td><td align='center'>1</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>41</td></tr>
<tr><th align='right'>80</th><td align='right'>3402</td><td>Virdemar</td><td align='center'>1</td><td>L2</td><td>hand</td><td>hand</td><td align='right'>41</td></tr>
<tr><th align='right'>81</th><td align='right'>3333</td><td>AmoebaAnts</td><td align='center'>2</td><td>L1</td><td>higher</td><td>OCaml</td><td align='right'>168</td></tr>
<tr><th align='right'>82</th><td align='right'>3208</td><td>Funktion im Kopf der</td><td align='center'>8</td><td>L2</td><td>unkn</td><td>unknown</td><td align='right'>42</td></tr>
<tr><th align='right'>83</th><td align='right'>3177</td><td>Funktion im Kopf der</td><td align='center'>8</td><td>L1</td><td>unkn</td><td>unknown</td><td align='right'>49</td></tr>
<tr><th align='right'>84</th><td align='right'>3016</td><td>ANTisocial</td><td align='center'>1</td><td>L1</td><td>higher</td><td>OCaml</td><td align='right'>513</td></tr>
<tr><th align='right'>85</th><td align='right'>2892</td><td>Teenage Mutated Ninj</td><td align='center'>3</td><td>L1</td><td>mut</td><td>C</td><td align='right'>9999</td></tr>
<tr><th align='right'>86</th><td align='right'>2619</td><td>Teenage Mutated Ninj</td><td align='center'>3</td><td>L2</td><td>mut</td><td>C</td><td align='right'>9998</td></tr>
<tr><th align='right'>87</th><td align='right'>2568</td><td>SIGO</td><td align='center'>1</td><td>L1</td><td>hand</td><td>hand</td><td align='right'>30</td></tr>
</table>

</center>
</td></tr>

<tr><td class="red"><b><a name="standings-main">Full Main Division Results</a></b></td></tr>
<tr><td>
<center><table>
<tr><th>Place</th> <th>Points</th> <th>Team</th> <th>Team size</th> <th>Ant</th> <th>Approach</th> <th>Language</th> <th>Ant size</th></tr>
<tr><th align='right'>1</th><td align='right'>142147</td><td>Dunkosmiloolump</td><td align='center'>4</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>3104</td></tr>
<tr><th align='right'>2</th><td align='right'>141947</td><td>Dunkosmiloolump</td><td align='center'>4</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>3134</td></tr>
<tr><th align='right'>3</th><td align='right'>138306</td><td>Frictionless Bananas</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>8004</td></tr>
<tr><th align='right'>4</th><td align='right'>137619</td><td>hasKilled</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>2834</td></tr>
<tr><th align='right'>5</th><td align='right'>136980</td><td>anichkov</td><td align='center'>3</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>8558</td></tr>
<tr><th align='right'>6</th><td align='right'>136241</td><td>RedTeam</td><td align='center'>7</td><td>M1</td><td>higher</td><td>Perl</td><td align='right'>1386</td></tr>
<tr><th align='right'>7</th><td align='right'>135972</td><td>Three-headed monkey </td><td align='center'>4</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>190</td></tr>
<tr><th align='right'>8</th><td align='right'>135950</td><td>Antsier</td><td align='center'>3</td><td>M1</td><td>higher</td><td>C</td><td align='right'>430</td></tr>
<tr><th align='right'>9</th><td align='right'>135612</td><td>defendant</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>788</td></tr>
<tr><th align='right'>10</th><td align='right'>135586</td><td>anichkov</td><td align='center'>3</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>8480</td></tr>
<tr><th align='right'>11</th><td align='right'>135231</td><td>Antsier</td><td align='center'>3</td><td>M2</td><td>higher</td><td>C</td><td align='right'>420</td></tr>
<tr><th align='right'>12</th><td align='right'>134834</td><td>RedTeam</td><td align='center'>7</td><td>M2</td><td>higher</td><td>Perl</td><td align='right'>1054</td></tr>
<tr><th align='right'>13</th><td align='right'>134810</td><td>Linepithema humile</td><td align='center'>2</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>382</td></tr>
<tr><th align='right'>14</th><td align='right'>134387</td><td>Matt Kearse</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>5022</td></tr>
<tr><th align='right'>15</th><td align='right'>134386</td><td>ERX</td><td align='center'>3</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>2936</td></tr>
<tr><th align='right'>16</th><td align='right'>134198</td><td>4060TEAM</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>5928</td></tr>
<tr><th align='right'>17</th><td align='right'>134183</td><td>ERX</td><td align='center'>3</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>2811</td></tr>
<tr><th align='right'>18</th><td align='right'>133661</td><td>Siegers</td><td align='center'>2</td><td>M1</td><td>higher</td><td>C</td><td align='right'>8159</td></tr>
<tr><th align='right'>19</th><td align='right'>133659</td><td>Ant-PLTer</td><td align='center'>7</td><td>M1</td><td>higher</td><td>Scheme</td><td align='right'>867</td></tr>
<tr><th align='right'>20</th><td align='right'>133633</td><td>Ant-PLTer</td><td align='center'>7</td><td>M2</td><td>higher</td><td>Scheme</td><td align='right'>867</td></tr>
<tr><th align='right'>21</th><td align='right'>133581</td><td>Matt Kearse</td><td align='center'>1</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>5022</td></tr>
<tr><th align='right'>22</th><td align='right'>133021</td><td>Funktion im Kopf der</td><td align='center'>9</td><td>M2</td><td>higher</td><td>Lisp</td><td align='right'>2981</td></tr>
<tr><th align='right'>23</th><td align='right'>132500</td><td>KillerAnt</td><td align='center'>2</td><td>M2</td><td>pre</td><td>C#</td><td align='right'>965</td></tr>
<tr><th align='right'>24</th><td align='right'>132151</td><td>Memento</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>546</td></tr>
<tr><th align='right'>25</th><td align='right'>132134</td><td>4060TEAM</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Python</td><td align='right'>6474</td></tr>
<tr><th align='right'>26</th><td align='right'>132046</td><td>Z25</td><td align='center'>2</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>2394</td></tr>
<tr><th align='right'>27</th><td align='right'>132024</td><td>Frictionless Bananas</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>7092</td></tr>
<tr><th align='right'>28</th><td align='right'>131617</td><td>kuma-</td><td align='center'>3</td><td>M1</td><td>pre</td><td>Ruby</td><td align='right'>4450</td></tr>
<tr><th align='right'>29</th><td align='right'>131411</td><td>Funktion im Kopf der</td><td align='center'>9</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>2411</td></tr>
<tr><th align='right'>30</th><td align='right'>130935</td><td>KillerAnt</td><td align='center'>2</td><td>M1</td><td>pre</td><td>C#</td><td align='right'>759</td></tr>
<tr><th align='right'>31</th><td align='right'>130057</td><td>FormiX</td><td align='center'>3</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>984</td></tr>
<tr><th align='right'>32</th><td align='right'>129763</td><td>mutAnts</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>237</td></tr>
<tr><th align='right'>33</th><td align='right'>128592</td><td>FormiX</td><td align='center'>3</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>1054</td></tr>
<tr><th align='right'>34</th><td align='right'>128130</td><td>mutAnts</td><td align='center'>2</td><td>M2</td><td>pre</td><td>Java</td><td align='right'>216</td></tr>
<tr><th align='right'>35</th><td align='right'>126092</td><td>team IseriaQueen and</td><td align='center'>5</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>334</td></tr>
<tr><th align='right'>36</th><td align='right'>125568</td><td>luvtechno</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>875</td></tr>
<tr><th align='right'>37</th><td align='right'>125448</td><td>The Caml Riders</td><td align='center'>7</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>668</td></tr>
<tr><th align='right'>38</th><td align='right'>125417</td><td>The Caml Riders</td><td align='center'>7</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>668</td></tr>
<tr><th align='right'>39</th><td align='right'>125057</td><td>team IseriaQueen and</td><td align='center'>5</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>335</td></tr>
<tr><th align='right'>40</th><td align='right'>124911</td><td>hasKilled</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>2056</td></tr>
<tr><th align='right'>41</th><td align='right'>123881</td><td>NiceAnts</td><td align='center'>4</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>253</td></tr>
<tr><th align='right'>42</th><td align='right'>122939</td><td>Trants</td><td align='center'>3</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>6513</td></tr>
<tr><th align='right'>43</th><td align='right'>122789</td><td>Absent-minded Dreame</td><td align='center'>5</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>5293</td></tr>
<tr><th align='right'>44</th><td align='right'>122215</td><td>Pants</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>2705</td></tr>
<tr><th align='right'>45</th><td align='right'>122143</td><td>OYATU-kit-SOS!</td><td align='center'>11</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>5227</td></tr>
<tr><th align='right'>46</th><td align='right'>121895</td><td>Poppo Mayaya</td><td align='center'>1</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>929</td></tr>
<tr><th align='right'>47</th><td align='right'>121884</td><td>PersistAnt</td><td align='center'>2</td><td>M1</td><td>pre</td><td>C#</td><td align='right'>159</td></tr>
<tr><th align='right'>48</th><td align='right'>121112</td><td>Death by Duxx</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Python</td><td align='right'>750</td></tr>
<tr><th align='right'>49</th><td align='right'>120977</td><td>Team Spoon</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Python</td><td align='right'>4827</td></tr>
<tr><th align='right'>50</th><td align='right'>120436</td><td>Team Ocant</td><td align='center'>10</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>5235</td></tr>
<tr><th align='right'>51</th><td align='right'>120338</td><td>Team Ocant</td><td align='center'>10</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>6933</td></tr>
<tr><th align='right'>52</th><td align='right'>119972</td><td>???</td><td align='center'>4</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>492</td></tr>
<tr><th align='right'>53</th><td align='right'>119532</td><td>KaNT</td><td align='center'>4</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>311</td></tr>
<tr><th align='right'>54</th><td align='right'>119290</td><td>Arbeitskreis Spielku</td><td align='center'>2</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>106</td></tr>
<tr><th align='right'>55</th><td align='right'>118885</td><td>pruessde</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>831</td></tr>
<tr><th align='right'>56</th><td align='right'>118588</td><td>C929B</td><td align='center'>3</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>391</td></tr>
<tr><th align='right'>57</th><td align='right'>118423</td><td>Camltron 5000</td><td align='center'>1</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>1098</td></tr>
<tr><th align='right'>58</th><td align='right'>118299</td><td>Team Spoon</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>9687</td></tr>
<tr><th align='right'>59</th><td align='right'>117872</td><td>MiMtim</td><td align='center'>4</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>257</td></tr>
<tr><th align='right'>60</th><td align='right'>117842</td><td>NiceAnts</td><td align='center'>4</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>936</td></tr>
<tr><th align='right'>61</th><td align='right'>117539</td><td>TAPLAS-tiny</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>536</td></tr>
<tr><th align='right'>62</th><td align='right'>117503</td><td>Death by Duxx</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>666</td></tr>
<tr><th align='right'>63</th><td align='right'>117379</td><td>Pants</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Python</td><td align='right'>6380</td></tr>
<tr><th align='right'>64</th><td align='right'>117272</td><td>Tycon Mismatch</td><td align='center'>6</td><td>M2</td><td>higher</td><td>SML</td><td align='right'>184</td></tr>
<tr><th align='right'>65</th><td align='right'>116509</td><td>Scott Family</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Revolution</td><td align='right'>228</td></tr>
<tr><th align='right'>66</th><td align='right'>115313</td><td>Team PacSoft</td><td align='center'>6</td><td>M2</td><td></td><td>Haskell</td><td align='right'>2805</td></tr>
<tr><th align='right'>67</th><td align='right'>114718</td><td>???</td><td align='center'>4</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>516</td></tr>
<tr><th align='right'>68</th><td align='right'>114564</td><td>phANTomas</td><td align='center'>1</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>8671</td></tr>
<tr><th align='right'>69</th><td align='right'>114086</td><td>LAMP</td><td align='center'>8</td><td>M1</td><td>higher</td><td>Scala</td><td align='right'>550</td></tr>
<tr><th align='right'>70</th><td align='right'>113738</td><td>SPb SU NT</td><td align='center'>2</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>279</td></tr>
<tr><th align='right'>71</th><td align='right'>113457</td><td>Trants</td><td align='center'>3</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>996</td></tr>
<tr><th align='right'>72</th><td align='right'>112554</td><td>Tycon Mismatch</td><td align='center'>6</td><td>M1</td><td>higher</td><td>SML</td><td align='right'>656</td></tr>
<tr><th align='right'>73</th><td align='right'>112458</td><td>Hand Crafted Code</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C</td><td align='right'>100</td></tr>
<tr><th align='right'>74</th><td align='right'>112376</td><td>OmnipotANT and the C</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>300</td></tr>
<tr><th align='right'>75</th><td align='right'>111970</td><td>Team XLERB</td><td align='center'>1</td><td>M1</td><td>pre</td><td>m4</td><td align='right'>372</td></tr>
<tr><th align='right'>76</th><td align='right'>111533</td><td>Team OaSys</td><td align='center'>4</td><td>M2</td><td>higher</td><td>Perl</td><td align='right'>3582</td></tr>
<tr><th align='right'>77</th><td align='right'>111021</td><td>ByteBrothers</td><td align='center'>2</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>543</td></tr>
<tr><th align='right'>78</th><td align='right'>110930</td><td>TAPLAS-tiny</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>305</td></tr>
<tr><th align='right'>79</th><td align='right'>110716</td><td>Dumb Python Ants</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>122</td></tr>
<tr><th align='right'>80</th><td align='right'>108968</td><td>300 Brave Ants From </td><td align='center'>1</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>765</td></tr>
<tr><th align='right'>81</th><td align='right'>108686</td><td>Absent-minded Dreame</td><td align='center'>5</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>5330</td></tr>
<tr><th align='right'>82</th><td align='right'>108368</td><td>phANTomas</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>7963</td></tr>
<tr><th align='right'>83</th><td align='right'>108317</td><td>Melting Pot</td><td align='center'>5</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>1929</td></tr>
<tr><th align='right'>84</th><td align='right'>108052</td><td>K.I.S.S.</td><td align='center'>2</td><td>M2</td><td>pre</td><td>Python</td><td align='right'>1937</td></tr>
<tr><th align='right'>85</th><td align='right'>107709</td><td>Formicoidies</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>1954</td></tr>
<tr><th align='right'>86</th><td align='right'>107219</td><td>shinichiro.h</td><td align='center'>1</td><td>M1</td><td>pre</td><td>D</td><td align='right'>3590</td></tr>
<tr><th align='right'>87</th><td align='right'>106857</td><td>SPb SU NT</td><td align='center'>2</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>285</td></tr>
<tr><th align='right'>88</th><td align='right'>106710</td><td>K.I.S.S.</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>358</td></tr>
<tr><th align='right'>89</th><td align='right'>106616</td><td>WiNniPeSauKee</td><td align='center'>6</td><td>M2</td><td>higher</td><td>Ruby</td><td align='right'>913</td></tr>
<tr><th align='right'>90</th><td align='right'>105941</td><td>ByteBrothers</td><td align='center'>2</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>483</td></tr>
<tr><th align='right'>91</th><td align='right'>105625</td><td>KaNT</td><td align='center'>4</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>99</td></tr>
<tr><th align='right'>92</th><td align='right'>105570</td><td>LackOf</td><td align='center'>7</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>420</td></tr>
<tr><th align='right'>93</th><td align='right'>105428</td><td>Ex Falso Quodlibet</td><td align='center'>4</td><td>M1</td><td>pre</td><td>Haskell</td><td align='right'>285</td></tr>
<tr><th align='right'>94</th><td align='right'>105351</td><td>Ex Falso Quodlibet</td><td align='center'>4</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>285</td></tr>
<tr><th align='right'>95</th><td align='right'>104934</td><td>Ex Falso Quodlibet</td><td align='center'>4</td><td>M2</td><td>pre</td><td>Haskell</td><td align='right'>305</td></tr>
<tr><th align='right'>96</th><td align='right'>104842</td><td>Ex Falso Quodlibet</td><td align='center'>4</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>305</td></tr>
<tr><th align='right'>97</th><td align='right'>104409</td><td>Three-headed monkey </td><td align='center'>4</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>402</td></tr>
<tr><th align='right'>98</th><td align='right'>103729</td><td>Ants Of Prey</td><td align='center'>5</td><td>M1</td><td>higher</td><td>m4</td><td align='right'>4335</td></tr>
<tr><th align='right'>99</th><td align='right'>103121</td><td>Captain Bluebear</td><td align='center'>1</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>2100</td></tr>
<tr><th align='right'>100</th><td align='right'>102645</td><td>jabber.ru</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Tcl</td><td align='right'>5904</td></tr>
<tr><th align='right'>101</th><td align='right'>101849</td><td>MiMtim</td><td align='center'>4</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>296</td></tr>
<tr><th align='right'>102</th><td align='right'>101816</td><td>Captain Bluebear</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>1986</td></tr>
<tr><th align='right'>103</th><td align='right'>100733</td><td>jabber.ru</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Tcl</td><td align='right'>5904</td></tr>
<tr><th align='right'>104</th><td align='right'>100457</td><td>Camltron 5000</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>1134</td></tr>
<tr><th align='right'>105</th><td align='right'>100444</td><td>Up Too Late</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Scheme</td><td align='right'>156</td></tr>
<tr><th align='right'>106</th><td align='right'>100242</td><td>The Code Junkies</td><td align='center'>3</td><td>M2</td><td>mut</td><td>C++</td><td align='right'>406</td></tr>
<tr><th align='right'>107</th><td align='right'>99971</td><td>Network172</td><td align='center'>1</td><td>M1</td><td></td><td>C#</td><td align='right'>1545</td></tr>
<tr><th align='right'>108</th><td align='right'>99907</td><td>The Code Junkies</td><td align='center'>3</td><td>M1</td><td>mut</td><td>C++</td><td align='right'>604</td></tr>
<tr><th align='right'>109</th><td align='right'>99692</td><td>September2</td><td align='center'>2</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>798</td></tr>
<tr><th align='right'>110</th><td align='right'>98666</td><td>BioDiesel</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>309</td></tr>
<tr><th align='right'>111</th><td align='right'>98450</td><td>September2</td><td align='center'>2</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>869</td></tr>
<tr><th align='right'>112</th><td align='right'>97268</td><td>BioDiesel</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>283</td></tr>
<tr><th align='right'>113</th><td align='right'>96551</td><td>Loud and Red</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Scheme</td><td align='right'>169</td></tr>
<tr><th align='right'>114</th><td align='right'>96218</td><td>Exo-plugarite Zulang</td><td align='center'>4</td><td>M1</td><td>pre</td><td>SML</td><td align='right'>1237</td></tr>
<tr><th align='right'>115</th><td align='right'>95975</td><td>Team AA (double-A). </td><td align='center'>2</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>767</td></tr>
<tr><th align='right'>116</th><td align='right'>95905</td><td>RhineCodeJugglers</td><td align='center'>2</td><td>M2</td><td></td><td>Pascal</td><td align='right'>30</td></tr>
<tr><th align='right'>117</th><td align='right'>95609</td><td>WiNniPeSauKee</td><td align='center'>6</td><td>M1</td><td>higher</td><td>Ruby</td><td align='right'>277</td></tr>
<tr><th align='right'>118</th><td align='right'>95548</td><td>Myrmedons</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Scheme</td><td align='right'>242</td></tr>
<tr><th align='right'>119</th><td align='right'>95154</td><td>dCoy</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>55</td></tr>
<tr><th align='right'>120</th><td align='right'>94567</td><td>Busman Holiday Club</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Lisp</td><td align='right'>114</td></tr>
<tr><th align='right'>121</th><td align='right'>94356</td><td>Anthill Inside</td><td align='center'>2</td><td>M2</td><td></td><td>Haskell</td><td align='right'>1023</td></tr>
<tr><th align='right'>122</th><td align='right'>93921</td><td>volkard</td><td align='center'>1</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>2530</td></tr>
<tr><th align='right'>123</th><td align='right'>93524</td><td>kuma-</td><td align='center'>3</td><td>M2</td><td>pre</td><td>Ruby</td><td align='right'>3938</td></tr>
<tr><th align='right'>124</th><td align='right'>93180</td><td>DDT</td><td align='center'>3</td><td>M1</td><td>pre</td><td>Haskell</td><td align='right'>6188</td></tr>
<tr><th align='right'>125</th><td align='right'>92917</td><td>SynthAnt</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Scheme</td><td align='right'>372</td></tr>
<tr><th align='right'>126</th><td align='right'>92525</td><td>antz-bros</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Lisp</td><td align='right'>230</td></tr>
<tr><th align='right'>127</th><td align='right'>92280</td><td>Homecoming</td><td align='center'>1</td><td>M2</td><td>higher</td><td>C</td><td align='right'>139</td></tr>
<tr><th align='right'>128</th><td align='right'>92054</td><td>Road Crew</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>223</td></tr>
<tr><th align='right'>129</th><td align='right'>91437</td><td>Antenitas</td><td align='center'>9</td><td>M2</td><td>pre</td><td>Pascal</td><td align='right'>200</td></tr>
<tr><th align='right'>130</th><td align='right'>91395</td><td>Network172</td><td align='center'>1</td><td>M2</td><td></td><td>C#</td><td align='right'>757</td></tr>
<tr><th align='right'>131</th><td align='right'>91114</td><td>Drunk Sed</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C</td><td align='right'>1651</td></tr>
<tr><th align='right'>132</th><td align='right'>91034</td><td>The Stansifer Family</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>1523</td></tr>
<tr><th align='right'>133</th><td align='right'>91002</td><td>Homecoming</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C</td><td align='right'>139</td></tr>
<tr><th align='right'>134</th><td align='right'>90763</td><td>RAI Software</td><td align='center'>4</td><td>M1</td><td>higher</td><td>C#</td><td align='right'>378</td></tr>
<tr><th align='right'>135</th><td align='right'>89961</td><td>RAI Software</td><td align='center'>4</td><td>M2</td><td>higher</td><td>C#</td><td align='right'>378</td></tr>
<tr><th align='right'>136</th><td align='right'>89681</td><td>Team OaSys</td><td align='center'>4</td><td>M1</td><td>higher</td><td>Perl</td><td align='right'>138</td></tr>
<tr><th align='right'>137</th><td align='right'>89421</td><td>DylAntz</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Perl</td><td align='right'>565</td></tr>
<tr><th align='right'>138</th><td align='right'>88618</td><td>Sense Here 115 1 Mar</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>5447</td></tr>
<tr><th align='right'>139</th><td align='right'>88170</td><td>Phase IV</td><td align='center'>1</td><td>M2</td><td>mut</td><td>C</td><td align='right'>206</td></tr>
<tr><th align='right'>140</th><td align='right'>87720</td><td>pruessde</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>830</td></tr>
<tr><th align='right'>141</th><td align='right'>87675</td><td>Rise of Ants</td><td align='center'>7</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>163</td></tr>
<tr><th align='right'>142</th><td align='right'>87492</td><td>Myrmedons</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Scheme</td><td align='right'>216</td></tr>
<tr><th align='right'>143</th><td align='right'>87337</td><td>Drunk Sed</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C</td><td align='right'>1238</td></tr>
<tr><th align='right'>144</th><td align='right'>87157</td><td>DylAntz</td><td align='center'>1</td><td>M2</td><td>higher</td><td>Perl</td><td align='right'>553</td></tr>
<tr><th align='right'>145</th><td align='right'>86745</td><td>MutAnts</td><td align='center'>9</td><td>M1</td><td>mut</td><td>C++</td><td align='right'>125</td></tr>
<tr><th align='right'>146</th><td align='right'>86460</td><td>The Slimey Ones</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>196</td></tr>
<tr><th align='right'>147</th><td align='right'>85061</td><td>Anthill Inside</td><td align='center'>2</td><td>M1</td><td></td><td>Haskell</td><td align='right'>2498</td></tr>
<tr><th align='right'>148</th><td align='right'>84124</td><td>BLUBBER</td><td align='center'>2</td><td>M1</td><td>pre</td><td>bash</td><td align='right'>38</td></tr>
<tr><th align='right'>149</th><td align='right'>82943</td><td>Team Lone Haskeller</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Haskell</td><td align='right'>2014</td></tr>
<tr><th align='right'>150</th><td align='right'>82933</td><td>antz-bros</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>251</td></tr>
<tr><th align='right'>151</th><td align='right'>82688</td><td>HexDEF6</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Haskell</td><td align='right'>194</td></tr>
<tr><th align='right'>152</th><td align='right'>82505</td><td>Anttrax</td><td align='center'>6</td><td>M1</td><td>higher</td><td>Alice</td><td align='right'>3571</td></tr>
<tr><th align='right'>153</th><td align='right'>82032</td><td>Grace_Siggi_and_Kids</td><td align='center'>4</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>377</td></tr>
<tr><th align='right'>154</th><td align='right'>81778</td><td>Formica silesiensis</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Python</td><td align='right'>794</td></tr>
<tr><th align='right'>155</th><td align='right'>81641</td><td>kapet</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>175</td></tr>
<tr><th align='right'>156</th><td align='right'>81522</td><td>SPb</td><td align='center'>0</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>4538</td></tr>
<tr><th align='right'>157</th><td align='right'>81164</td><td>Team Lone Haskeller</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Haskell</td><td align='right'>1710</td></tr>
<tr><th align='right'>158</th><td align='right'>80816</td><td>Grace_Siggi_and_Kids</td><td align='center'>4</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>388</td></tr>
<tr><th align='right'>159</th><td align='right'>80688</td><td>ANTagoniste</td><td align='center'>2</td><td>M1</td><td>higher</td><td>C</td><td align='right'>286</td></tr>
<tr><th align='right'>160</th><td align='right'>80495</td><td>Formica silesiensis</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>682</td></tr>
<tr><th align='right'>161</th><td align='right'>79020</td><td>LAMP</td><td align='center'>8</td><td>M2</td><td>higher</td><td>Scala</td><td align='right'>422</td></tr>
<tr><th align='right'>162</th><td align='right'>78681</td><td>MutAnts</td><td align='center'>9</td><td>M2</td><td>mut</td><td>C++</td><td align='right'>125</td></tr>
<tr><th align='right'>163</th><td align='right'>78579</td><td>Simantics</td><td align='center'>6</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>22</td></tr>
<tr><th align='right'>164</th><td align='right'>78190</td><td>Thuringia</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>74</td></tr>
<tr><th align='right'>165</th><td align='right'>77411</td><td>No Repro</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C#</td><td align='right'>70</td></tr>
<tr><th align='right'>166</th><td align='right'>77059</td><td>The Stansifer Family</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>759</td></tr>
<tr><th align='right'>167</th><td align='right'>76859</td><td>Simantics</td><td align='center'>6</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>161</td></tr>
<tr><th align='right'>168</th><td align='right'>76346</td><td>Packi</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Pascal</td><td align='right'>159</td></tr>
<tr><th align='right'>169</th><td align='right'>76079</td><td>No Repro</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C#</td><td align='right'>75</td></tr>
<tr><th align='right'>170</th><td align='right'>76076</td><td>SPb</td><td align='center'>0</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>5075</td></tr>
<tr><th align='right'>171</th><td align='right'>76019</td><td>Team XLERB</td><td align='center'>1</td><td>M2</td><td>pre</td><td>m4</td><td align='right'>28</td></tr>
<tr><th align='right'>172</th><td align='right'>75867</td><td>Loud and Red</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Scheme</td><td align='right'>98</td></tr>
<tr><th align='right'>173</th><td align='right'>75083</td><td>apple2gs</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>611</td></tr>
<tr><th align='right'>174</th><td align='right'>74724</td><td>IHI</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Ruby</td><td align='right'>554</td></tr>
<tr><th align='right'>175</th><td align='right'>74252</td><td>Leftturn</td><td align='center'>3</td><td>M1</td><td>pre</td><td>C</td><td align='right'>288</td></tr>
<tr><th align='right'>176</th><td align='right'>74145</td><td>Leftturn</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C</td><td align='right'>288</td></tr>
<tr><th align='right'>177</th><td align='right'>73991</td><td>Sense Here 115 1 Mar</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Lisp</td><td align='right'>7586</td></tr>
<tr><th align='right'>178</th><td align='right'>73313</td><td>AKW311</td><td align='center'>1</td><td>M1</td><td>pre</td><td>SML</td><td align='right'>732</td></tr>
<tr><th align='right'>179</th><td align='right'>73308</td><td>GUIGNOL</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>1365</td></tr>
<tr><th align='right'>180</th><td align='right'>72998</td><td>Arbeitskreis Spielku</td><td align='center'>2</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>27</td></tr>
<tr><th align='right'>181</th><td align='right'>72414</td><td>Gansevles</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>141</td></tr>
<tr><th align='right'>182</th><td align='right'>72002</td><td>Babyfoot</td><td align='center'>5</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>126</td></tr>
<tr><th align='right'>183</th><td align='right'>71258</td><td>SpaceAnt</td><td align='center'>2</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>35</td></tr>
<tr><th align='right'>184</th><td align='right'>70852</td><td>AKW311</td><td align='center'>1</td><td>M2</td><td>pre</td><td>SML</td><td align='right'>720</td></tr>
<tr><th align='right'>185</th><td align='right'>69937</td><td>PicoAnts</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>30</td></tr>
<tr><th align='right'>186</th><td align='right'>69839</td><td>Hand Crafted Code</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C</td><td align='right'>21</td></tr>
<tr><th align='right'>187</th><td align='right'>69566</td><td>Antenitas</td><td align='center'>9</td><td>M1</td><td>pre</td><td>Pascal</td><td align='right'>200</td></tr>
<tr><th align='right'>188</th><td align='right'>69115</td><td>ANTagoniste</td><td align='center'>2</td><td>M2</td><td>higher</td><td>C</td><td align='right'>64</td></tr>
<tr><th align='right'>189</th><td align='right'>68820</td><td>KISS-Gang</td><td align='center'>4</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>16</td></tr>
<tr><th align='right'>190</th><td align='right'>68208</td><td>Black Ice</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>18</td></tr>
<tr><th align='right'>191</th><td align='right'>68194</td><td>Team AA (double-A). </td><td align='center'>2</td><td>M2</td><td>pre</td><td>Python</td><td align='right'>474</td></tr>
<tr><th align='right'>192</th><td align='right'>67867</td><td>Black Ice</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>18</td></tr>
<tr><th align='right'>193</th><td align='right'>66935</td><td>LIX Ants</td><td align='center'>3</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>12</td></tr>
<tr><th align='right'>194</th><td align='right'>66852</td><td>Ants Forever</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>22</td></tr>
<tr><th align='right'>195</th><td align='right'>66092</td><td>Codefeed</td><td align='center'>1</td><td>M2</td><td>higher</td><td>C#</td><td align='right'>81</td></tr>
<tr><th align='right'>196</th><td align='right'>65916</td><td>Qwghlm</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>1451</td></tr>
<tr><th align='right'>197</th><td align='right'>65888</td><td>uguu.org</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>60</td></tr>
<tr><th align='right'>198</th><td align='right'>65017</td><td>ZASKAR'S ANTS</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Basic</td><td align='right'>4721</td></tr>
<tr><th align='right'>199</th><td align='right'>64300</td><td>PPuiSsant</td><td align='center'>5</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>296</td></tr>
<tr><th align='right'>200</th><td align='right'>64093</td><td>PicoAnts</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>30</td></tr>
<tr><th align='right'>201</th><td align='right'>63750</td><td>RhineCodeJugglers</td><td align='center'>2</td><td>M1</td><td></td><td>Pascal</td><td align='right'>10</td></tr>
<tr><th align='right'>202</th><td align='right'>62880</td><td>OYATU-kit-SOS!</td><td align='center'>11</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>31</td></tr>
<tr><th align='right'>203</th><td align='right'>62848</td><td>ANTisocial</td><td align='center'>1</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>334</td></tr>
<tr><th align='right'>204</th><td align='right'>62112</td><td>The Nemerlies</td><td align='center'>6</td><td>M1</td><td>higher</td><td>Nemerle</td><td align='right'>2935</td></tr>
<tr><th align='right'>205</th><td align='right'>62077</td><td>Les Lampions</td><td align='center'>6</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>160</td></tr>
<tr><th align='right'>206</th><td align='right'>62031</td><td>Packi</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Pascal</td><td align='right'>78</td></tr>
<tr><th align='right'>207</th><td align='right'>61868</td><td>Kent's Mutant Space </td><td align='center'>3</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>786</td></tr>
<tr><th align='right'>208</th><td align='right'>61858</td><td>DDT</td><td align='center'>3</td><td>M2</td><td>pre</td><td>Haskell</td><td align='right'>1710</td></tr>
<tr><th align='right'>209</th><td align='right'>61791</td><td>Kent's Mutant Space </td><td align='center'>3</td><td>M2</td><td>higher</td><td>Python</td><td align='right'>786</td></tr>
<tr><th align='right'>210</th><td align='right'>61749</td><td>Chan-Subburam</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>47</td></tr>
<tr><th align='right'>211</th><td align='right'>61724</td><td>mir</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>363</td></tr>
<tr><th align='right'>212</th><td align='right'>61526</td><td>The Al-Gore-Rhythms</td><td align='center'>3</td><td>M1</td><td>mut</td><td>Java</td><td align='right'>526</td></tr>
<tr><th align='right'>213</th><td align='right'>61490</td><td>mstorti</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>89</td></tr>
<tr><th align='right'>214</th><td align='right'>61354</td><td>Chan-Subburam</td><td align='center'>2</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>48</td></tr>
<tr><th align='right'>215</th><td align='right'>61089</td><td>Igel</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>21</td></tr>
<tr><th align='right'>216</th><td align='right'>60955</td><td>Team PacSoft</td><td align='center'>6</td><td>M1</td><td></td><td>Haskell</td><td align='right'>4409</td></tr>
<tr><th align='right'>217</th><td align='right'>60941</td><td>geneticant</td><td align='center'>1</td><td>M1</td><td>mut</td><td>C++</td><td align='right'>351</td></tr>
<tr><th align='right'>218</th><td align='right'>60848</td><td>I, MySelf and Kurama</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>5</td></tr>
<tr><th align='right'>219</th><td align='right'>60338</td><td>Sealab 2021</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Python</td><td align='right'>86</td></tr>
<tr><th align='right'>220</th><td align='right'>60234</td><td>ANTisocial</td><td align='center'>1</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>369</td></tr>
<tr><th align='right'>221</th><td align='right'>59957</td><td>Leftturn</td><td align='center'>3</td><td>M2</td><td>pre</td><td>C</td><td align='right'>30</td></tr>
<tr><th align='right'>222</th><td align='right'>59860</td><td>epsilon-ant</td><td align='center'>1</td><td>M1</td><td>higher</td><td>GNUepsilon</td><td align='right'>1888</td></tr>
<tr><th align='right'>223</th><td align='right'>59447</td><td>Hollandians</td><td align='center'>2</td><td>M1</td><td>mut</td><td>C</td><td align='right'>8501</td></tr>
<tr><th align='right'>224</th><td align='right'>59234</td><td>KISS-Gang</td><td align='center'>4</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>19</td></tr>
<tr><th align='right'>225</th><td align='right'>58726</td><td>Oxmo Team</td><td align='center'>3</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>119</td></tr>
<tr><th align='right'>226</th><td align='right'>58644</td><td>HCOOH</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>41</td></tr>
<tr><th align='right'>227</th><td align='right'>57957</td><td>Yasuhiro Furuta</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>303</td></tr>
<tr><th align='right'>228</th><td align='right'>57120</td><td>slime</td><td align='center'>2</td><td>M1</td><td></td><td>Lisp</td><td align='right'>143</td></tr>
<tr><th align='right'>229</th><td align='right'>56490</td><td>Scott Family</td><td align='center'>2</td><td>M2</td><td>pre</td><td>Revolution</td><td align='right'>49</td></tr>
<tr><th align='right'>230</th><td align='right'>56381</td><td>Hollandians</td><td align='center'>2</td><td>M2</td><td>mut</td><td>C</td><td align='right'>5528</td></tr>
<tr><th align='right'>231</th><td align='right'>55902</td><td>mstorti</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>55</td></tr>
<tr><th align='right'>232</th><td align='right'>55312</td><td>The Al-Gore-Rhythms</td><td align='center'>3</td><td>M2</td><td>mut</td><td>Java</td><td align='right'>529</td></tr>
<tr><th align='right'>233</th><td align='right'>55074</td><td>Merry Mercurians</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Mercury</td><td align='right'>1640</td></tr>
<tr><th align='right'>234</th><td align='right'>54793</td><td>uguu.org</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>9029</td></tr>
<tr><th align='right'>235</th><td align='right'>54640</td><td>Merry Mercurians</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Mercury</td><td align='right'>473</td></tr>
<tr><th align='right'>236</th><td align='right'>54511</td><td>Phase IV</td><td align='center'>1</td><td>M1</td><td>mut</td><td>C</td><td align='right'>189</td></tr>
<tr><th align='right'>237</th><td align='right'>54390</td><td>Captain Bluebear</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>54</td></tr>
<tr><th align='right'>238</th><td align='right'>51455</td><td>Team Monkeys</td><td align='center'>3</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>298</td></tr>
<tr><th align='right'>239</th><td align='right'>50869</td><td>Detlef Pleiss</td><td align='center'>1</td><td>M2</td><td>mut</td><td>Java</td><td align='right'>16</td></tr>
<tr><th align='right'>240</th><td align='right'>50861</td><td>Detlef Pleiss</td><td align='center'>1</td><td>M1</td><td>mut</td><td>Java</td><td align='right'>16</td></tr>
<tr><th align='right'>241</th><td align='right'>50668</td><td>BrainBug</td><td align='center'>1</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>54</td></tr>
<tr><th align='right'>242</th><td align='right'>50364</td><td>Sabertooth Penguin</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Haskell</td><td align='right'>315</td></tr>
<tr><th align='right'>243</th><td align='right'>49943</td><td>Why Bother</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Lisp</td><td align='right'>67</td></tr>
<tr><th align='right'>244</th><td align='right'>48981</td><td>geneticant</td><td align='center'>1</td><td>M2</td><td>mut</td><td>C++</td><td align='right'>361</td></tr>
<tr><th align='right'>245</th><td align='right'>48919</td><td>PPuiSsant</td><td align='center'>5</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>258</td></tr>
<tr><th align='right'>246</th><td align='right'>48588</td><td>bassclar</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>60</td></tr>
<tr><th align='right'>247</th><td align='right'>47764</td><td>NIHAOMAYI</td><td align='center'>1</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>9834</td></tr>
<tr><th align='right'>248</th><td align='right'>47621</td><td>NIHAOMAYI</td><td align='center'>1</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>9834</td></tr>
<tr><th align='right'>249</th><td align='right'>46947</td><td>Hendrik Spohr</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>830</td></tr>
<tr><th align='right'>250</th><td align='right'>46938</td><td>AcidCode</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>5333</td></tr>
<tr><th align='right'>251</th><td align='right'>46237</td><td>Hitorikko</td><td align='center'>1</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>129</td></tr>
<tr><th align='right'>252</th><td align='right'>45419</td><td>Formicoidies</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>2011</td></tr>
<tr><th align='right'>253</th><td align='right'>45258</td><td>AcidCode</td><td align='center'>1</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>350</td></tr>
<tr><th align='right'>254</th><td align='right'>44903</td><td>Hendrik Spohr</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>825</td></tr>
<tr><th align='right'>255</th><td align='right'>44403</td><td>Z-Dyne</td><td align='center'>1</td><td>M1</td><td>mut</td><td>Python</td><td align='right'>89</td></tr>
<tr><th align='right'>256</th><td align='right'>43433</td><td>Rise of Ants</td><td align='center'>7</td><td>M2</td><td>pre</td><td>Java</td><td align='right'>116</td></tr>
<tr><th align='right'>257</th><td align='right'>43076</td><td>We-Need-No-Stinking-</td><td align='center'>3</td><td>M1</td><td>mut</td><td>C</td><td align='right'>3048</td></tr>
<tr><th align='right'>258</th><td align='right'>42190</td><td>We-Need-No-Stinking-</td><td align='center'>3</td><td>M2</td><td>mut</td><td>C</td><td align='right'>9460</td></tr>
<tr><th align='right'>259</th><td align='right'>41998</td><td>Z-Dyne</td><td align='center'>1</td><td>M2</td><td>mut</td><td>Python</td><td align='right'>133</td></tr>
<tr><th align='right'>260</th><td align='right'>41760</td><td>IP Team</td><td align='center'>4</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>985</td></tr>
<tr><th align='right'>261</th><td align='right'>41630</td><td>Bloody Camls</td><td align='center'>3</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>17</td></tr>
<tr><th align='right'>262</th><td align='right'>41126</td><td>FUColombia</td><td align='center'>3</td><td>M1</td><td>higher</td><td>Scheme</td><td align='right'>50</td></tr>
<tr><th align='right'>263</th><td align='right'>40998</td><td>The Nemerlies</td><td align='center'>6</td><td>M2</td><td>higher</td><td>Nemerle</td><td align='right'>2479</td></tr>
<tr><th align='right'>264</th><td align='right'>40433</td><td>OneManWeekendFun</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>38</td></tr>
<tr><th align='right'>265</th><td align='right'>39972</td><td>Team Cool</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>346</td></tr>
<tr><th align='right'>266</th><td align='right'>39929</td><td>Team Cool</td><td align='center'>2</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>347</td></tr>
<tr><th align='right'>267</th><td align='right'>39078</td><td>Merion</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>36</td></tr>
<tr><th align='right'>268</th><td align='right'>38570</td><td>GREEK_CODING_FORCE</td><td align='center'>2</td><td>M1</td><td>mut</td><td>C++</td><td align='right'>377</td></tr>
<tr><th align='right'>269</th><td align='right'>38500</td><td>AmoebaAnts</td><td align='center'>2</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>344</td></tr>
<tr><th align='right'>270</th><td align='right'>37225</td><td>Codefeed</td><td align='center'>1</td><td>M1</td><td>higher</td><td>C#</td><td align='right'>172</td></tr>
<tr><th align='right'>271</th><td align='right'>37063</td><td>State_not_found</td><td align='center'>2</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>7462</td></tr>
<tr><th align='right'>272</th><td align='right'>36904</td><td>Team TUHH</td><td align='center'>3</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>113</td></tr>
<tr><th align='right'>273</th><td align='right'>36836</td><td>Team TUHH</td><td align='center'>3</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>80</td></tr>
<tr><th align='right'>274</th><td align='right'>36667</td><td>State_not_found</td><td align='center'>2</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>7462</td></tr>
<tr><th align='right'>275</th><td align='right'>36401</td><td>Merion</td><td align='center'>1</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>29</td></tr>
<tr><th align='right'>276</th><td align='right'>34834</td><td>Team Incomplete & Ti</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>112</td></tr>
<tr><th align='right'>277</th><td align='right'>33876</td><td>Prologin</td><td align='center'>2</td><td>M1</td><td>higher</td><td>C++</td><td align='right'>2030</td></tr>
<tr><th align='right'>278</th><td align='right'>33798</td><td>E.N.S.T : Every Nigh</td><td align='center'>5</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>79</td></tr>
<tr><th align='right'>279</th><td align='right'>33639</td><td>IP Team</td><td align='center'>4</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>1864</td></tr>
<tr><th align='right'>280</th><td align='right'>33469</td><td>OneManWeekendFun</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>17</td></tr>
<tr><th align='right'>281</th><td align='right'>33351</td><td>Team Xyzzy</td><td align='center'>2</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>196</td></tr>
<tr><th align='right'>282</th><td align='right'>32313</td><td>random boke</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C</td><td align='right'>31</td></tr>
<tr><th align='right'>283</th><td align='right'>32297</td><td>Insane Ant Posse</td><td align='center'>2</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>593</td></tr>
<tr><th align='right'>284</th><td align='right'>32026</td><td>Disciples of Ikam (N</td><td align='center'>4</td><td>M2</td><td>mut</td><td>OCaml</td><td align='right'>146</td></tr>
<tr><th align='right'>285</th><td align='right'>31903</td><td>Disciples of Ikam (N</td><td align='center'>4</td><td>M1</td><td>mut</td><td>OCaml</td><td align='right'>9999</td></tr>
<tr><th align='right'>286</th><td align='right'>31466</td><td>SynthAnt</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Scheme</td><td align='right'>55</td></tr>
<tr><th align='right'>287</th><td align='right'>31147</td><td>random boke</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C</td><td align='right'>5810</td></tr>
<tr><th align='right'>288</th><td align='right'>30824</td><td>Antsimilation</td><td align='center'>1</td><td>M2</td><td></td><td>Haskell</td><td align='right'>80</td></tr>
<tr><th align='right'>289</th><td align='right'>30376</td><td>Les Lampions</td><td align='center'>6</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>20</td></tr>
<tr><th align='right'>290</th><td align='right'>30168</td><td>Andrey Stolyarov</td><td align='center'>1</td><td>M2</td><td>pre</td><td>C++</td><td align='right'>154</td></tr>
<tr><th align='right'>291</th><td align='right'>30075</td><td>Antsimilation</td><td align='center'>1</td><td>M1</td><td></td><td>Haskell</td><td align='right'>79</td></tr>
<tr><th align='right'>292</th><td align='right'>29386</td><td>Prologin</td><td align='center'>2</td><td>M2</td><td>higher</td><td>C++</td><td align='right'>2738</td></tr>
<tr><th align='right'>293</th><td align='right'>28507</td><td>C929B</td><td align='center'>3</td><td>M2</td><td>pre</td><td>OCaml</td><td align='right'>205</td></tr>
<tr><th align='right'>294</th><td align='right'>28205</td><td>Bushwhackers</td><td align='center'>4</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>48</td></tr>
<tr><th align='right'>295</th><td align='right'>27725</td><td>Andrey Stolyarov</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>153</td></tr>
<tr><th align='right'>296</th><td align='right'>27506</td><td>RandomDirection</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>1056</td></tr>
<tr><th align='right'>297</th><td align='right'>27141</td><td>Warren Lispnik</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>5069</td></tr>
<tr><th align='right'>298</th><td align='right'>26845</td><td>lollipop</td><td align='center'>1</td><td>M1</td><td>pre</td><td>OCaml</td><td align='right'>75</td></tr>
<tr><th align='right'>299</th><td align='right'>26769</td><td>Ants Making Smalltal</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Smalltalk</td><td align='right'>3961</td></tr>
<tr><th align='right'>300</th><td align='right'>26708</td><td>NiceTry</td><td align='center'>2</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>27</td></tr>
<tr><th align='right'>301</th><td align='right'>26661</td><td>Ants Making Smalltal</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Smalltalk</td><td align='right'>3961</td></tr>
<tr><th align='right'>302</th><td align='right'>25718</td><td>dkondr</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>16</td></tr>
<tr><th align='right'>303</th><td align='right'>25423</td><td>Sabertooth Penguin</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Haskell</td><td align='right'>302</td></tr>
<tr><th align='right'>304</th><td align='right'>24707</td><td>TeamMahalito</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>548</td></tr>
<tr><th align='right'>305</th><td align='right'>24267</td><td>JJK</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>37</td></tr>
<tr><th align='right'>306</th><td align='right'>24046</td><td>Bloody Camls</td><td align='center'>3</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>1747</td></tr>
<tr><th align='right'>307</th><td align='right'>23602</td><td>United Ant Power</td><td align='center'>3</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>59</td></tr>
<tr><th align='right'>308</th><td align='right'>23535</td><td>Otnäs Ormtjusarna</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Lisp</td><td align='right'>843</td></tr>
<tr><th align='right'>309</th><td align='right'>23530</td><td>vbkilled</td><td align='center'>2</td><td>M1</td><td>mut</td><td>Basic</td><td align='right'>50</td></tr>
<tr><th align='right'>310</th><td align='right'>23309</td><td>PLanT</td><td align='center'>5</td><td>M1</td><td>higher</td><td>Scheme</td><td align='right'>820</td></tr>
<tr><th align='right'>311</th><td align='right'>22996</td><td>The Green Onions</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>403</td></tr>
<tr><th align='right'>312</th><td align='right'>22459</td><td>Team Zope</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Python</td><td align='right'>191</td></tr>
<tr><th align='right'>313</th><td align='right'>22412</td><td>Tony Blair Ants</td><td align='center'>3</td><td>M1</td><td>oth</td><td>Java</td><td align='right'>166</td></tr>
<tr><th align='right'>314</th><td align='right'>22303</td><td>Team Cavalears</td><td align='center'>2</td><td>M2</td><td>higher</td><td>Java</td><td align='right'>239</td></tr>
<tr><th align='right'>315</th><td align='right'>22206</td><td>SpaceAnt</td><td align='center'>2</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>15</td></tr>
<tr><th align='right'>316</th><td align='right'>22172</td><td>Team Cavalears</td><td align='center'>2</td><td>M1</td><td>higher</td><td>Java</td><td align='right'>278</td></tr>
<tr><th align='right'>317</th><td align='right'>22019</td><td>The Giver</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Ruby</td><td align='right'>129</td></tr>
<tr><th align='right'>318</th><td align='right'>20030</td><td>Bushwhackers</td><td align='center'>4</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>51</td></tr>
<tr><th align='right'>319</th><td align='right'>19974</td><td>Igel</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>29</td></tr>
<tr><th align='right'>320</th><td align='right'>19027</td><td>fhqwhgads</td><td align='center'>1</td><td>M2</td><td>pre</td><td>Java</td><td align='right'>24</td></tr>
<tr><th align='right'>321</th><td align='right'>19011</td><td>fhqwhgads</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>22</td></tr>
<tr><th align='right'>322</th><td align='right'>18562</td><td>Oxmo Team</td><td align='center'>3</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>199</td></tr>
<tr><th align='right'>323</th><td align='right'>18546</td><td>Erlant Savant</td><td align='center'>1</td><td>M1</td><td></td><td>Erlang</td><td align='right'>117</td></tr>
<tr><th align='right'>324</th><td align='right'>18351</td><td>Erlant Savant</td><td align='center'>1</td><td>M2</td><td></td><td>Erlang</td><td align='right'>118</td></tr>
<tr><th align='right'>325</th><td align='right'>18339</td><td>SenteAnt</td><td align='center'>1</td><td>M2</td><td>mut</td><td>Lisp</td><td align='right'>10000</td></tr>
<tr><th align='right'>326</th><td align='right'>17906</td><td>Sunday Monday Tuesda</td><td align='center'>3</td><td>M1</td><td>pre</td><td>Java</td><td align='right'>3802</td></tr>
<tr><th align='right'>327</th><td align='right'>17872</td><td>lochan.org</td><td align='center'>1</td><td>M1</td><td>higher</td><td>Haskell</td><td align='right'>900</td></tr>
<tr><th align='right'>328</th><td align='right'>17730</td><td>JASTeam</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>56</td></tr>
<tr><th align='right'>329</th><td align='right'>17287</td><td>eDespot</td><td align='center'>2</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>29</td></tr>
<tr><th align='right'>330</th><td align='right'>17164</td><td>1</td><td align='center'>1</td><td>M1</td><td>pre</td><td>C++</td><td align='right'>8924</td></tr>
<tr><th align='right'>331</th><td align='right'>15841</td><td>SenteAnt</td><td align='center'>1</td><td>M1</td><td>mut</td><td>Lisp</td><td align='right'>10000</td></tr>
<tr><th align='right'>332</th><td align='right'>15735</td><td>FSC</td><td align='center'>7</td><td>M2</td><td>pre</td><td>Perl</td><td align='right'>296</td></tr>
<tr><th align='right'>333</th><td align='right'>13786</td><td>Ants in your pants</td><td align='center'>3</td><td>M2</td><td>mut</td><td>Scheme</td><td align='right'>127</td></tr>
<tr><th align='right'>334</th><td align='right'>13710</td><td>All Your Food Are Be</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Lisp</td><td align='right'>370</td></tr>
<tr><th align='right'>335</th><td align='right'>13701</td><td>Dennis Okon</td><td align='center'>1</td><td>M1</td><td>mut</td><td>C#</td><td align='right'>1024</td></tr>
<tr><th align='right'>336</th><td align='right'>12914</td><td>Dennis Okon</td><td align='center'>1</td><td>M2</td><td>mut</td><td>C#</td><td align='right'>1024</td></tr>
<tr><th align='right'>337</th><td align='right'>11908</td><td>I, MySelf and Kurama</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>26</td></tr>
<tr><th align='right'>338</th><td align='right'>11413</td><td>defendant</td><td align='center'>1</td><td>M2</td><td>higher</td><td>Haskell</td><td align='right'>752</td></tr>
<tr><th align='right'>339</th><td align='right'>11241</td><td>PLanT</td><td align='center'>5</td><td>M2</td><td>higher</td><td>Scheme</td><td align='right'>692</td></tr>
<tr><th align='right'>340</th><td align='right'>10862</td><td>FUColombia</td><td align='center'>3</td><td>M2</td><td>higher</td><td>Scheme</td><td align='right'>1219</td></tr>
<tr><th align='right'>341</th><td align='right'>10116</td><td>intellitek</td><td align='center'>1</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>250</td></tr>
<tr><th align='right'>342</th><td align='right'>7516</td><td>Flavor</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>61</td></tr>
<tr><th align='right'>343</th><td align='right'>7490</td><td>LIX Ants</td><td align='center'>3</td><td>M1</td><td>higher</td><td>OCaml</td><td align='right'>756</td></tr>
<tr><th align='right'>344</th><td align='right'>6823</td><td>Ants in your pants</td><td align='center'>3</td><td>M1</td><td>mut</td><td>Scheme</td><td align='right'>127</td></tr>
<tr><th align='right'>345</th><td align='right'>6820</td><td>Virdemar</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>41</td></tr>
<tr><th align='right'>346</th><td align='right'>6817</td><td>Antigone</td><td align='center'>1</td><td>M1</td><td>mut</td><td>Java</td><td align='right'>10000</td></tr>
<tr><th align='right'>347</th><td align='right'>6791</td><td>Antigone</td><td align='center'>1</td><td>M2</td><td>mut</td><td>Java</td><td align='right'>10000</td></tr>
<tr><th align='right'>348</th><td align='right'>6609</td><td>Virdemar</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>41</td></tr>
<tr><th align='right'>349</th><td align='right'>6599</td><td>GrinderFX</td><td align='center'>1</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>33</td></tr>
<tr><th align='right'>350</th><td align='right'>6459</td><td>Funktion im Kopf der</td><td align='center'>8</td><td>M2</td><td>unkn</td><td>unknown</td><td align='right'>42</td></tr>
<tr><th align='right'>351</th><td align='right'>6446</td><td>Funktion im Kopf der</td><td align='center'>8</td><td>M1</td><td>unkn</td><td>unknown</td><td align='right'>49</td></tr>
<tr><th align='right'>352</th><td align='right'>6073</td><td>FSC</td><td align='center'>7</td><td>M1</td><td>pre</td><td>Perl</td><td align='right'>2371</td></tr>
<tr><th align='right'>353</th><td align='right'>6055</td><td>eDespot</td><td align='center'>2</td><td>M2</td><td>hand</td><td>hand</td><td align='right'>34</td></tr>
<tr><th align='right'>354</th><td align='right'>5931</td><td>SIGO</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>30</td></tr>
<tr><th align='right'>355</th><td align='right'>5856</td><td>Freenode #scheme ICF</td><td align='center'>5</td><td>M1</td><td></td><td>Scheme</td><td align='right'>359</td></tr>
<tr><th align='right'>356</th><td align='right'>5831</td><td>GrinderFX</td><td align='center'>1</td><td>M1</td><td>hand</td><td>hand</td><td align='right'>35</td></tr>
<tr><th align='right'>357</th><td align='right'>5789</td><td>Freenode #scheme ICF</td><td align='center'>5</td><td>M2</td><td></td><td>Scheme</td><td align='right'>159</td></tr>
<tr><th align='right'>358</th><td align='right'>5726</td><td>Teenage Mutated Ninj</td><td align='center'>3</td><td>M1</td><td>mut</td><td>C</td><td align='right'>9999</td></tr>
<tr><th align='right'>359</th><td align='right'>5545</td><td>Babyfoot</td><td align='center'>5</td><td>M2</td><td>higher</td><td>OCaml</td><td align='right'>477</td></tr>
<tr><th align='right'>360</th><td align='right'>5442</td><td>Teenage Mutated Ninj</td><td align='center'>3</td><td>M2</td><td>mut</td><td>C</td><td align='right'>9998</td></tr>
<tr><th align='right'>361</th><td align='right'>4451</td><td>Non seq</td><td align='center'>1</td><td>M1</td><td>pre</td><td>Ruby</td><td align='right'>2</td></tr>
</table>
</center>
</tr></td>

<tr><td class="red"><b><a name="languages">Language Statistics</a></b></td></tr>
<tr><td>
<center><table>
<tr><td>25</td><td>C++           </td></tr>
<tr><td>24</td><td>OCaml	 </td></tr>
<tr><td>23</td><td>hand coded	 </td></tr>
<tr><td>21</td><td>Java		 </td></tr>
<tr><td>20</td><td>Haskell	 </td></tr>
<tr><td>16</td><td>Python	 </td></tr>
<tr><td>15</td><td>C		 </td></tr>
<tr><td>12</td><td>Lisp		 </td></tr>
<tr><td>11</td><td>Perl		 </td></tr>
<tr><td>9</td><td>Scheme	 </td></tr>
<tr><td>8</td><td>unknown	 </td></tr>
<tr><td>7</td><td>C#		 </td></tr>
<tr><td>5</td><td>Ruby		 </td></tr>
<tr><td>5</td><td>Pascal	 </td></tr>
<tr><td>2</td><td>SML		 </td></tr>
<tr><td>2</td><td>Basic		 </td></tr>
<tr><td>2</td><td>m4		 </td></tr>
<tr><td>1</td><td>Mercury	 </td></tr>
<tr><td>1</td><td>Scala		 </td></tr>
<tr><td>1</td><td>Erlang	 </td></tr>
<tr><td>1</td><td>Tcl		 </td></tr>
<tr><td>1</td><td>D		 </td></tr>
<tr><td>1</td><td>Alice		 </td></tr>
<tr><td>1</td><td>GNUepsilon	 </td></tr>
<tr><td>1</td><td>Nemerle	 </td></tr>
<tr><td>1</td><td>bash		 </td></tr>
<tr><td>1</td><td>Revolution	 </td></tr>
<tr><td>1</td><td>Smalltalk	 </td></tr>
</table></center>
</tr></td>			 
				 
</table>			 

<?php include("footer.php") ?>
