let style = "
* {
    font-size: 11pt
}

html {
    font-family: sans-serif;
    padding: 0;
    margin: 0;
    /* font-size: 8pt; */
}

body {
    padding-left: 10px;
    padding-right: 10px;
    padding-bottom: 10px;
    margin: 0;
    max-width: 800px;
}

table {
    width: 100%;
    border: 1px solid;
    border-collapse: collapse;
    /* max-width: 1400px; */
    /* table-layout: fixed; */
}

h1 {
    font-size: 11pt;
    margin-top: 16pt;
}

tr {
    padding : 0;
    margin : 0;
}

th, td {
    text-align: left;
    vertical-align: top;
    border-left: 1px solid;
    border-right: 1px solid;
    padding-left: 5px;
    padding-right: 5px;
    padding-top: 3px;
    padding-bottom: 3px;
}

th {
    padding-top: 5px;
    padding-bottom: 5px;
}

th {
    font-weight: normal;
    font-style: italic;
}

.pagelinks {
    padding-top: 10px;
    padding-bottom: 30px;
}

#pages .page { display: none }
#pages .page:target { display: block }

#pages .pagelinks .button, 
#pages .pagelinks .inactive_button { 
  padding-top: 5px; 
  padding-bottom: 5px;
  padding-left: 10px; 
  padding-right: 10px;
  display: inline-block;
}





@media (prefers-color-scheme: dark) {

    html {
        background-color: black;
        color: lightgray;
    }

    table, th, td {
        border-color: #303030;
    }

    tr {
        background-color: #181818;
    }

    th {
        background-color: #252525;
        border-bottom: 1px solid #303030;
    }

    tr:hover {
        background-color: #101044;
    }

    #pages .pagelinks .button, 
    #pages .pagelinks .inactive_button { 
        background-color: white;
        border: 1px solid #EEEEEE;
    }

    #pages .pagelinks .button:hover {
        background-color: #BBBBBB;
    }

    #pages .pagelinks .button a { 
        color: black;
        text-decoration: none;
    }

    .pagelinks .inactive_button {
        color: #AAAAAA;
    }

}



@media (prefers-color-scheme: light) {

    html {
        background-color: white;
        color: black;
    }

    table, th, td {
        border-color: #E9E9E9;
    }

    tr {
        background-color: #F8F8F8;
    }

    th {
        background-color: #F0F0F0;
        border-bottom: 1px solid #E9E9E9;
    }

    tr:hover {
        background-color: #E2F0FF;
    }

    #pages .pagelinks .button, 
    #pages .pagelinks .inactive_button { 
        background-color: black;
        border: 1px solid #111111;
    }

    #pages .pagelinks .button:hover {
        background-color: #444444;
    }

    #pages .pagelinks .button a { 
        color: white;
        text-decoration: none;
    }

    .pagelinks .inactive_button {
        color: #555555;
    }
}
"
