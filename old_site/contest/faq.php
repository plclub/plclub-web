<?php 
      $this_page = "faq"; 
      $version = '$Id: faq.php,v 1.9 2004/06/07 01:00:36 sumii Exp $';
      include("header.php") 
?>
  <table>
  <tr><td class="red"><b>During the contest</b></td></tr>
  <tr><td>

    <p><b>Wouldn't <tt>s<sub>i</sub></tt> become too large after
    100,000 rounds?</b><br>

    Please note that Section 2.10 "Number Theory" gives a mathematical
    description of the random numbers generator, not an implementation
    algorithm.

    <p><b>My random numbers generator agrees with yours, but my
    simulator traces diverge from yours after step <tt>nnn</tt>.  Can
    your simulator have a bug?</b><br>

    The sample ant is very random, and certain situations in the ant
    world happen <em>for the first time</em> only well after the start
    of the game, so your first diverging round number <tt>nnn</tt> can
    be pretty large.

    <p><b>Where is the contest registration page?</b><br>

    There is no registration for the contest -- just submit your entry
    before the deadline.  You can submit multiple times -- the last
    accepted entry is the one that will count.
  
    <p><b>How will announcements be made?</b><br>

    All announcements will be posted to the <a
    href="http://lists.seas.upenn.edu/mailman/listinfo/icfp04-participants">participants
    mailing list</a>. Be sure to join it to receive these important
    messages. Especially important announcements will also be posted
    to the <a href="news.php">news</a> page.

    <p><b>How do I contact the organizers directly?</b><br>Messages sent to
    <tt>icfp04-organizers@lists.seas.upenn.edu</tt> will be received by the 
    contest organizers.<p>

  </td></tr>

  <tr><td class="red"><b>Submission Format and Computing Resources</b></td></tr>
  <tr><td>

  <p><b>What will the submission format be?</b><br>

    Your entry to the contest will be a plain text file in a format that
    we will specify in the task description.
    <p>
    You may write your entry entirely by hand, or generate it using
    tools in a programming language of your choice; we will ask you to
    submit the source code for these tools (if any) along with your
    entry, and we will look at them for purposes of awarding the judges'
    prize, but we will not need to run your tools on our machines.

  <p><b>What character code should I use for my ant programs?</b><br>

    ASCII.  Any of "\n" (LF), "\r\n" (CR + LF), or "\r" (CR) is OK
    for the end of a line.  Each instruction line (including the last
    one) should end with one of them.

  <p><b>What kind of computing environment will be used to run and
  judge contest results?</b><br>

  All submissions will ultimately be judged using our own
  machines. 

  <p><b>Do I need a supercomputer to win?</b><br>

  While we can't say for sure that having access to some big iron
  won't help, the contest task will be designed so that competitors
  without access to extraordinary resources can still win.<p>

  </td></tr>

  <tr><td class="red"><b>Internet Connection</b></td></tr>
  <tr><td>

    <p><b>Will I need my computer to be hooked up to the Internet for a
    long time?</b><br> 

    No. You will need an Internet connection, but only for relatively
    short periods of time.

    <p><b>Will bandwidth/latency/reliability of the link matter?</b><br>
    It must work some of the time! But a dial-up modem will be fine.

    <p><b>My machine is behind a firewall. Will I be able to enter?</b><br>
    If you can read this page, your connection will work just fine.<p>
  </td></tr>

  <tr><td class="red"><b>Other questions</b></td></tr>
  <tr><td>

    <p><b>Is there going to be a 24-hour lightning division?</b><br> Yes. Teams
    may submit an entry by Saturday 5 June, 12:00 noon (EDT) for
    consideration in the 24-hour lightning division. Teams may enter
    both the lightning division and the regular competition.

    <p><b>How much does it cost to enter the contest?</b><br>
    Nothing! Participation in the contest is free. There is no registration fee.

    <p><b>What are the rules for programming teams?</b><br>
    We encourage everyone to enter! Teams may be individuals or groups
    of any size including faculty, students, and non-academics. There
    is one exception to this rule: the <a href="team.php">contest
    organizers</a> are ineligible.

    <p><b>What will be the method for task access and result submission?</b><br>

    The task will be disseminated from this web site. Entries will be
    submitted over the Internet. The exact details will be included in
    the task description.

    <p><b>What format will the task description be in?</b><br>
    Postscript, PDF and HTML.

    <p><b>What will I need to read it?</b><br>Any web browser should do.<p>

  </td></tr>
  </table>


<?php include("footer.php") ?>



