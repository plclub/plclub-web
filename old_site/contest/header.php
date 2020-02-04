<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN"> 

<html>
<head>
<title>ICFP Programming Contest 2004</title>
<link rel="stylesheet" href="style.css">
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
</head>

<body>

<table class="green"><tr>
<td><img src="contest.gif" alt="Contest Ant Logo"/></td>
<td align="center"><h1>The Seventh Antual ICFP Programming Contest</h1></td></tr></table><p>

<table class="gray">
<tr><td>
  <table><tr><td style="vertical-align:top">
  <table style="width : 100px"> 

<?php 

/* script to print the blue boxes on the LHS of the page
 *
 * parameterized on the variable $this_page so that the 
 * blue box denoting the current page is NOT a link and 
 * is printed with a dashed outline (td.b)
 */

/* all of the pages: names map to their printed names */
$allpages = array("index" => "Main", 
		  "intro" => "Introduction",
		  "news" => "News", 
		  "dates" => "Dates", 
		  "faq" => "FAQ", 
		  "rules" => "Rules",
		  "results" => "Results",
		  "task" => "Task", 
		  "lists" => "Lists", 
		  "team" => "Team", 
		  "history" => "History");

foreach ($allpages as $page => $Page) {

  if (strcmp($this_page, $page) == 0) {
    $class = "b";
    $olink = $clink = "";
  } else {
    $class = "blue";
    $olink = "<a href=\"$page.php\">";
    $clink = "</a>";
  }
  print<<<EOF
<tr><td class="$class">$olink $Page $clink</td></tr>
EOF;
}
?>

  </table>
  </td><td style="vertical-align:top">
<!-- content -->
